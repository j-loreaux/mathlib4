/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public meta import Lean.Server.CodeActions.Provider
public import Mathlib.Init

/-!
# Code actions turning goals into `have`s

This file provides two code actions, offered on a tactic whenever the infoview shows goals there:

* "Turn goal into `have`" inserts `have name : type := by sorry`, where `type` is the first goal
  shown in the infoview and `name` is its tag;
* "Turn all goals into `have`s" does the same for each goal shown in the infoview.

The `have`s are inserted immediately before the tactic under the cursor, on their own lines, at
that tactic's indentation. A typical use is a tactic which leaves side goals (for instance
`simp_side`): turning these into `have`s placed before the tactic puts them in the local context
instead, where the tactic can use them.

## Implementation notes

* The goals are those the infoview shows (`Lean.Elab.InfoTree.goalsAt?`), normally the goals
  after the tactic under the cursor. The `have` is inserted before the innermost tactic in a tactic
  sequence that contains that tactic, so that the result is again a tactic sequence.
* The `have` is elaborated in the local context *before* that tactic, which may differ from the
  context of the goal. A local hypothesis of the goal is kept only if its name refers, at the
  insertion point, to the same hypothesis (or to one with the same type), and instances only if an
  instance of the same type is available there. The goal is universally quantified over all other
  local hypotheses it depends on, which in particular covers inaccessible ones (`h✝`).
* The name of the `have` is the last component of the goal's tag: for a hierarchical tag such as
  `mul_inv_cancel₀.h`, this is `h`. (A hierarchical name is accepted by `have`, but it is long and
  `h.left` would shadow the projection.) Anonymous, inaccessible or internal tags give `have :`.
  A name which already refers to a local hypothesis at the insertion point is replaced by a fresh
  one (`h_1`), so that the `have` does not shadow anything later tactics may refer to.
* Goals containing metavariables are skipped, since they cannot be stated as a `have`.
* The type is printed with `pp.proofs` and `pp.deepTerms` set, so that no `⋯` appears, and
  continuation lines are indented by four more spaces than the `have`.
-/

public meta section

namespace Mathlib.CodeAction.GoalToHave

open Lean Elab Meta Server Lsp RequestM

/-- The innermost element of a tactic sequence in `stx` whose range includes `r`, if any. -/
partial def innermostSeqTactic? (r : Syntax.Range) (stx : Syntax) (best : Option Syntax := none) :
    Option Syntax := Id.run do
  let list? :=
    if stx.isOfKind ``Parser.Tactic.tacticSeq1Indented then some stx[0]
    else if stx.isOfKind ``Parser.Tactic.tacticSeqBracketed then some stx[1]
    else none
  if let some list := list? then
    for tac in list.getSepArgs do
      if tac.getRange?.any (·.includes r) then
        return innermostSeqTactic? r tac (some tac)
    return best
  for arg in stx.getArgs do
    if arg.getRange?.any (·.includes r) then
      return innermostSeqTactic? r arg best
  return best

/-- The name of the `have` for a goal tagged `tag`, or `none` for an anonymous `have`. -/
def haveName? (tag : Name) : Option Name :=
  if tag.hasMacroScopes || tag.isInaccessibleUserName || tag.isInternal then none else
    match tag with
    | .str _ s => if s == "this" then none else some (.mkSimple s)
    | _ => none

/-- Whether the local declaration `d` of the goal's local context `lctx` is also available, under
the same name, in the local context `refLCtx` where the `have` will be elaborated. Instances need
not be named: it suffices that an instance of the same type is available. -/
def isAvailable (refLCtx lctx : LocalContext) (d : LocalDecl) : MetaM Bool := do
  let type ← instantiateMVars d.type
  if (← isClass? type).isSome then
    if refLCtx.contains d.fvarId then return true
    return ← refLCtx.anyM fun d' ↦ return (← instantiateMVars d'.type) == type
  let n := d.userName
  if n.hasMacroScopes || n.isInaccessibleUserName then return false
  -- `d` must not be shadowed in its own context
  unless (lctx.findFromUserName? n).any (·.fvarId == d.fvarId) do return false
  let some d' := refLCtx.findFromUserName? n | return false
  return d'.fvarId == d.fvarId || (← instantiateMVars d'.type) == type

/-- Replace the inaccessible binder names in the leading binders of `e` by accessible ones. -/
partial def sanitizeBinderNames : Expr → Expr
  | .forallE n t b bi => .forallE (sanitize n) t (sanitizeBinderNames b) bi
  | .letE n t v b nd => .letE (sanitize n) t v (sanitizeBinderNames b) nd
  | e => e
where
  /-- An accessible version of `n`. -/
  sanitize (n : Name) : Name :=
    let n := n.eraseMacroScopes
    if n.isAnonymous || n.isInaccessibleUserName || n.isInternal then `x else n

/-- The statement of the goal `g` as a closed term in the local context `refLCtx`: `g`'s target,
universally quantified over the local hypotheses it depends on which are not available in
`refLCtx`. Returns `none` if the goal contains metavariables. -/
def statement? (refLCtx : LocalContext) (g : MVarId) : MetaM (Option Expr) := g.withContext do
  let lctx ← getLCtx
  let target ← instantiateMVars (← g.getType)
  if target.hasMVar then return none
  let mut todo := (collectFVars {} target).fvarIds.toList
  let mut seen : FVarIdSet := {}
  let mut toAbstract : FVarIdSet := {}
  while true do
    let fvarId :: rest := todo | break
    todo := rest
    if seen.contains fvarId then continue
    seen := seen.insert fvarId
    let d ← fvarId.getDecl
    unless ← isAvailable refLCtx lctx d do
      toAbstract := toAbstract.insert fvarId
      let mut s := collectFVars {} (← instantiateMVars d.type)
      if let some v := d.value? then s := collectFVars s (← instantiateMVars v)
      todo := todo ++ s.fvarIds.toList
  let fvars := lctx.foldl (init := #[]) fun acc d ↦
    if toAbstract.contains d.fvarId then acc.push d.toExpr else acc
  let e ← instantiateMVars (← mkForallFVars fvars target (usedLetOnly := true))
  if e.hasMVar then return none
  return some (sanitizeBinderNames e)

/-- A goal which can be turned into a `have`. -/
structure HaveGoal where
  /-- The goal. -/
  goal : MVarId
  /-- Its statement (see `statement?`). It lives in the local context of `goal`, but only involves
  local hypotheses available, under the same name, at the insertion point. -/
  type : Expr

/-- The text of the `have`s for `goals`, one per line, each line but the first indented by `col`
spaces, and a fresh name for each named goal not clashing with the names in `refLCtx` and with each
other. -/
def haveText (refLCtx : LocalContext) (col : Nat) (goals : Array HaveGoal) : MetaM String := do
  let mut used : NameSet := refLCtx.foldl (init := {}) fun s d ↦ s.insert d.userName
  let mut lines := #[]
  for { goal, type } in goals do
    let head ← match haveName? (← goal.getTag) with
      | none => pure "have :"
      | some n => do
        let mut n' := n
        let mut i := 1
        while used.contains n' do
          n' := n.appendIndexAfter i
          i := i + 1
        used := used.insert n'
        pure s!"have {n'} :"
    -- `type` lives in the local context of `goal`, see `statement?`
    let fmt : Format := head ++ " " ++ .nest 4 (← goal.withContext <| ppExpr type) ++ " := by sorry"
    lines := lines.push (fmt.pretty (width := 100) (indent := col) (column := col))
  return ("\n".pushn ' ' col).intercalate lines.toList

/-- The code actions "Turn goal into `have`" and "Turn all goals into `have`s". -/
@[code_action_provider]
def goalToHave : CodeActionProvider := fun params snap ↦ do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos params.range.end
  let some { ctxInfo, tacticInfo := ti, useAfter, .. } :=
    (snap.infoTree.goalsAt? text hoverPos).head? | return #[]
  let goals := if useAfter then ti.goalsAfter else ti.goalsBefore
  if goals.isEmpty then return #[]
  -- the tactic before which the `have`s are inserted
  let some tiRange := ti.stx.getRange? | return #[]
  let some tgt := innermostSeqTactic? tiRange snap.stx | return #[]
  let some tgtRange := tgt.getRange? | return #[]
  let some tgtPos := tgt.getPos? | return #[]
  -- the local context in which the `have`s will be elaborated
  let tgtInfo? := if tgt.getKind == ti.stx.getKind && tgtRange == tiRange then some ti else
    match Lean.CodeAction.findInfoTree? tgt.getKind tgtRange (some ctxInfo) snap.infoTree
      (fun _ i ↦ i matches .ofTacticInfo _) (canonicalOnly := true) with
    | some (_, .node (.ofTacticInfo i) _) => some i
    | _ => none
  let some tgtInfo := tgtInfo? | return #[]
  let refLCtx := (tgtInfo.goalsBefore.head?.bind tgtInfo.mctxBefore.findDecl?).map (·.lctx)
    |>.getD {}
  let ctxInfo := { ctxInfo with
    mctx := if useAfter then ti.mctxAfter else ti.mctxBefore
    options := pp.deepTerms.set (pp.proofs.set ctxInfo.options true) true }
  let haveGoals ← ctxInfo.runMetaM {} do
    goals.toArray.filterMapM fun goal ↦ return (← statement? refLCtx goal).map ({ goal, type := · })
  let col := (text.toPosition tgtPos).column
  let mkAction (title : String) (goals : Array HaveGoal) : LazyCodeAction :=
    let eager := { title, kind? := "refactor.rewrite" }
    { eager, lazy? := some do
        let newText ← ctxInfo.runMetaM {} (haveText refLCtx col goals)
        let pos := text.utf8PosToLspPos tgtPos
        return { eager with
          edit? := some <| .ofTextEdit doc.versionedIdentifier
            { range := ⟨pos, pos⟩, newText := newText ++ "\n".pushn ' ' col } } }
  let mut actions := #[]
  if let some g := haveGoals[0]? then
    if g.goal == goals[0]! then
      actions := actions.push (mkAction "Turn goal into `have`" #[g])
  if haveGoals.size ≥ 2 then
    actions := actions.push (mkAction "Turn all goals into `have`s" haveGoals)
  return actions

end Mathlib.CodeAction.GoalToHave
