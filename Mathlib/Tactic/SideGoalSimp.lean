/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Sym
public meta import Lean.Meta.Tactic.TryThis
public meta import Mathlib.Lean.Elab.Tactic.FocusGoals
public import Mathlib.Init

/-!
# Simplification with side goals

`simp` can only use a conditional rewrite rule `h : P → a = b` once its discharger proves `P` on
the spot. Many tactics would rather rewrite now and deal with `P` later: they collect the side
conditions of a whole simplification, deduplicate them, and then hand them to a specialized
procedure (`fun_prop`, `positivity`, …) all at once, or return them to the user.

This file provides that, on top of the structural simplifier `Lean.Meta.Sym.Simp`. It replaces
its rewriting step `Lean.Meta.Sym.Simp.Theorem.rewrite` by `SideGoalTheorem.rewrite`, which turns
the hypotheses marked as side goals into fresh goals instead of discharging them.

## Design

* Which hypotheses become side goals is a property of the rewrite rule, not of the simplifier:
  a `SideGoalTheorem` is a `Sym.Simp.Theorem` together with the set of its hypotheses that become
  side goals. All the hypotheses are first given to the discharger, as usual. If it fails on a
  hypothesis marked as a side goal, that hypothesis becomes a side goal, and otherwise the rule
  does not apply.
* `Theorem.rewrite` matches inside `withNewMCtxDepth`, which discards every metavariable created
  while matching. So the side goals are first abstracted out of the instantiated theorem, and only
  created, at the outer depth, once the match is known to succeed.
* A side goal is created in the local context of the goal being simplified, not in the one of the
  subterm being rewritten: under a binder `x`, the side goal `P x` becomes `?h : ∀ x, P x`,
  used as `?h x`. This is what allows rewriting under binders.
* Side goals with the same statement are created only once.
* The side goals of a run of the simplifier are collected in an `IO.Ref`, since `Sym.Simp.SimpM`
  has no room for state of our own.

## Main declarations

* `SideGoalTheorem`, `SideGoalTheorems`: rewrite rules with side goals, and sets of them.
* `SideGoalTheorem.rewrite`, `SideGoalTheorems.rewrite`: the rewriting steps.
* `simpGoalWithSideGoals`: simplifies a goal, returning the simplified goal and the side goals.
* `register_side_goal_simp_attr`: registers an attribute `@[foo h₁ … hₙ]` for a set of rewrite
  rules, `h₁ … hₙ` being the hypotheses that become side goals (all of them by default).
* `@[side_goal_simp]`, `simp_side` and `simp_side?`: a default set of such rules, and tactics
  using it.
-/

public meta section

namespace Mathlib.Tactic.SideGoalSimp

open Lean Meta Elab Tactic Sym Lean.Meta.Sym.Simp

/-- A `Sym.simp` rewrite rule, some of whose hypotheses become side goals instead of being
discharged. -/
structure SideGoalTheorem where
  /-- The rewrite rule. -/
  thm : Theorem
  /-- Bit `i` is set iff the hypothesis bound to pattern variable `i` becomes a side goal. -/
  sideMask : Nat
  /-- The names of the side goals of the pattern variables: their binder names, prefixed by the
  name of the theorem, e.g. `mul_inv_cancel₀.h`. -/
  names : Array Name
  /-- The types of the pattern variables, as stated in the theorem, in terms of the universe
  parameters of its pattern. Unlike the types recorded in the pattern, reducible definitions are
  not unfolded in them, so they are used to state the side goals. -/
  binderTypes : Array Expr
  /-- The hypotheses which were asked to become side goals, or `#[]` if all the propositional
  hypotheses become side goals. -/
  sideGoals : Array Name := #[]
  deriving Inhabited

instance : BEq SideGoalTheorem where
  beq thm₁ thm₂ := thm₁.thm == thm₂.thm

/-- A set of `SideGoalTheorem`s, indexed by their left-hand sides. -/
structure SideGoalTheorems where
  /-- The rewrite rules. -/
  thms : DiscrTree SideGoalTheorem := {}
  deriving Inhabited

/-- Adds a rewrite rule to a set. -/
def SideGoalTheorems.insert (thms : SideGoalTheorems) (thm : SideGoalTheorem) :
    SideGoalTheorems :=
  ⟨insertPattern thms.thms thm.thm.pattern thm⟩

/-- Returns the binder names of the first `numVars` binders of `type`, the theorem `thm`, and the
mask of those that become side goals: the hypotheses named in `sideGoals` or, if it is empty, all
the propositions that are not instance arguments. -/
def mkSideMask (thm : MessageData) (type : Expr) (numVars : Nat) (sideGoals : Array Name) :
    MetaM (Array Name × Nat) :=
  forallBoundedTelescope type numVars fun xs _ ↦ do
    let mut names := #[]
    let mut mask := 0
    for h : i in [:xs.size] do
      let decl ← xs[i].fvarId!.getDecl
      names := names.push decl.userName
      if sideGoals.isEmpty then
        if !decl.binderInfo.isInstImplicit && (← isProp decl.type) then
          mask := mask ||| (1 <<< i)
      else if sideGoals.contains decl.userName then
        unless ← isProp decl.type do
          throwError "the hypothesis `{decl.userName}` cannot become a side goal, \
            it is not a proposition{indentExpr decl.type}"
        mask := mask ||| (1 <<< i)
    for name in sideGoals do
      unless names.contains name do
        throwError "{thm} has no hypothesis named `{name}`"
    return (names, mask)

/-- Returns the domains of the first `n` binders of `type`, with loose bound variables for the
previous binders, or `none` if `type` does not start with `n` binders. -/
def getBinderTypes? (type : Expr) (n : Nat) : Option (Array Expr) :=
  go type n #[]
where
  /-- Implementation of `getBinderTypes?`. -/
  go : Expr → Nat → Array Expr → Option (Array Expr)
    | _, 0, acc => some acc
    | .forallE _ d b _, n + 1, acc => go b n (acc.push d)
    | .mdata _ e, n, acc => go e n acc
    | _, _, _ => none

/-- Creates a `SideGoalTheorem` from the rewrite rule `thm`, called `name` and described by `what`
in error messages, whose type is `type`, with universe parameters `levelParams`. -/
def mkSideGoalTheorem (name : Name) (what : MessageData) (thm : Theorem) (type : Expr)
    (levelParams : List Name) (sideGoals : Array Name) : MetaM SideGoalTheorem := do
  let numVars := thm.pattern.varTypes.size
  let (names, sideMask) ← mkSideMask what type numVars sideGoals
  let names := names.map ((privateToUserName name).eraseMacroScopes ++ ·)
  let type := type.instantiateLevelParams levelParams (thm.pattern.levelParams.map mkLevelParam)
  let binderTypes := (getBinderTypes? type numVars).getD thm.pattern.varTypes
  return { thm, sideMask, names, binderTypes, sideGoals }

/-- Creates the rewrite rule `declName`, whose hypotheses `sideGoals` (all of them if it is empty)
become side goals. -/
def mkSideGoalTheoremFromDecl (declName : Name) (sideGoals : Array Name := #[]) :
    MetaM SideGoalTheorem := do
  let info ← getConstInfo declName
  mkSideGoalTheorem declName m!"`{.ofConstName declName}`" (← mkTheoremFromDecl declName)
    info.type info.levelParams sideGoals

/-- Creates the rewrite rule given by the proof `e`, whose hypotheses `sideGoals` (all of them if
it is empty) become side goals. The side goals are named after `e` if it is a local hypothesis. -/
def mkSideGoalTheoremFromExpr (e : Expr) (sideGoals : Array Name := #[]) :
    MetaM SideGoalTheorem := do
  let name ← if e.isFVar then e.fvarId!.getUserName else pure .anonymous
  mkSideGoalTheorem name m!"`{e}`" (← mkTheoremFromExpr e)
    (← instantiateMVars (← Meta.inferType e)) [] sideGoals

/-- The side goals created by a run of the simplifier. -/
structure SideGoals where
  /-- The side goals, in the order they were created. -/
  goals : Array MVarId := #[]
  /-- The side goal of each statement, so that side goals with the same statement are created
  only once. The key is the statement closed over the binders entered by the simplifier, after
  `shareCommon`: statements are identified up to α-equivalence and unfolding of reducible
  definitions, and the key is a pointer. -/
  byType : Std.HashMap ExprPtr Expr := {}
  /-- The rules which rewrote something, in the order they were first used. -/
  used : Array SideGoalTheorem := #[]
  deriving Inhabited

/-- What `SideGoalTheorem.rewrite` needs besides the rule and the term. -/
structure SideGoalContext where
  /-- The local context of the goal being simplified, where the side goals are created. -/
  lctx : LocalContext
  /-- The local instances of the goal being simplified. -/
  localInsts : LocalInstances
  /-- The discharger for the hypotheses that do not become side goals. -/
  disch : Discharger
  /-- The side goals created so far. -/
  ref : IO.Ref SideGoals

/-- The outcome of matching a `SideGoalTheorem` against a term. -/
inductive SideGoalMatch where
  /-- The rule does not apply. -/
  | failed (contextDependent : Bool)
  /-- The rule applies with universe levels `us` and arguments `args`, provided the side goals of
  types `sideTypes` are proved. The arguments are abstracted over the side goals, and each side
  goal type over the previous ones. `sideNames` are the names of the side goals. -/
  | ok (us : List Level) (args : Array Expr) (sideTypes : Array Expr) (sideNames : Array Name)
      (contextDependent : Bool)

/-- Returns `true` if `e` has a metavariable created after the first `mvarCounter` ones. -/
def hasNewMVar (mvarCounter : Nat) (e : Expr) : MetaM Bool := do
  if !e.hasMVar then return false
  (← getMVars e).anyM fun mvarId ↦ return (← mvarId.getDecl).index ≥ mvarCounter

/-- Matches the rule `thm` against `e`, discharging its hypotheses with `d`. Those which `d` does
not prove become side goals if they are marked as such, and otherwise the rule does not apply. This
mirrors the first half of `Lean.Meta.Sym.Simp.Theorem.rewrite`, except that the
instances that `Lean.Meta.Sym.Pattern.match?` could not synthesize are synthesized again, now that
the other arguments are known: `match?` synthesizes an instance before the instances it depends on
are assigned by unification. -/
def SideGoalTheorem.match (thm : SideGoalTheorem) (d : Discharger) (e : Expr) :
    Sym.Simp.SimpM SideGoalMatch := withNewMCtxDepth do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let some result ← thm.thm.pattern.match? e | return .failed false
  let us ← result.us.mapM instantiateLevelMVars
  let mut args := result.args
  let mut isCD := false
  let mut sides := #[]
  let mut sideTypes := #[]
  let mut sideNames := #[]
  for i in [:args.size] do
    let arg := args[i]!
    if let .mvar mvarId := arg then
      if ← mvarId.isAssigned then
        args := args.set! i (← instantiateMVarsS arg)
      else
        let decl ← mvarId.getDecl
        if decl.index ≥ mvarCounterSaved then
          if result.unresolvedInsts.contains mvarId then
            let some val ← Sym.synthInstance? (← instantiateMVars decl.type)
              | return .failed isCD
            let val ← if thm.thm.rhsVarMask.testBit i then shareCommon val else pure val
            mvarId.assign val
            args := args.set! i val
          else
            match ← d (← instantiateMVars decl.type) with
            | .failed cd =>
              isCD := isCD || cd
              unless thm.sideMask.testBit i do return .failed isCD
              let type := thm.binderTypes[i]!.instantiateLevelParams thm.thm.pattern.levelParams us
              let type ← instantiateMVars (type.instantiateRev (args.extract 0 i))
              sideTypes := sideTypes.push (type.abstract sides)
              sides := sides.push arg
              sideNames := sideNames.push (thm.names[i]?.getD .anonymous)
            | .solved val cd =>
              isCD := isCD || cd
              let val ← if thm.thm.rhsVarMask.testBit i then
                shareCommon (← instantiateMVars val)
              else
                instantiateMVars val
              mvarId.assign val
              args := args.set! i val
    else if arg.hasMVar then
      args := args.set! i (← instantiateMVarsS arg)
  args ← args.mapM fun arg ↦ do
    let arg ← instantiateMVars arg
    return if arg.hasMVar then arg.abstract sides else arg
  if ← (args ++ sideTypes).anyM fun e ↦ hasNewMVar mvarCounterSaved e then
    return .failed isCD
  return .ok us args sideTypes sideNames isCD

/-- Closes `type` over the free variables introduced since `lctx`, that is, by the simplifier
entering binders, which `type` depends on. Returns the closed type and the free variables to apply
a proof of it to. -/
def closeOverNewFVars (lctx : LocalContext) (type : Expr) : MetaM (Expr × Array Expr) := do
  let decls := (← getLCtx).decls.toArray.filterMap fun
    | some decl => if lctx.contains decl.fvarId then none else some decl
    | none => none
  let mut used := (collectFVars {} type).fvarSet
  let mut kept := #[]
  for decl in decls.reverse do
    if used.contains decl.fvarId then
      kept := kept.push decl
      used := (collectFVars (collectFVars { fvarSet := used } decl.type)
        (decl.value?.getD (mkSort .zero))).fvarSet
  kept := kept.reverse
  let closed ← mkForallFVars (kept.map (·.toExpr)) type
  return (closed, kept.filter (!·.isLet) |>.map (·.toExpr))

/-- Rewrites `e` with the rule `thm`, turning the hypotheses marked as side goals into goals
recorded in `ctx.ref`. This is `Lean.Meta.Sym.Simp.Theorem.rewrite`, with side goals. -/
def SideGoalTheorem.rewrite (thm : SideGoalTheorem) (ctx : SideGoalContext) (e : Expr) :
    Sym.Simp.SimpM Result := do
  let (us, args, sideTypes, sideNames, isCD) ← match ← thm.match ctx.disch e with
    | .failed cd => return mkRflResultCD cd
    | .ok us args sideTypes sideNames cd => pure (us, args, sideTypes, sideNames, cd)
  let state ← ctx.ref.get
  let mut byType := state.byType
  let mut newGoals := #[]
  let mut proofs := #[]
  for h : j in [:sideTypes.size] do
    let (type, xs) ← closeOverNewFVars ctx.lctx (sideTypes[j].instantiateRev proofs)
    let key ← shareCommon type
    let goal ← match byType[ExprPtr.mk key]? with
      | some goal => pure goal
      | none =>
        let goal ← mkFreshExprMVarAt ctx.lctx ctx.localInsts type .syntheticOpaque
          (sideNames[j]?.getD .anonymous)
        byType := byType.insert ⟨key⟩ goal
        newGoals := newGoals.push goal.mvarId!
        pure goal
    proofs := proofs.push (← shareCommon (mkAppN goal xs))
  let args ← args.mapM fun arg ↦
    if arg.hasLooseBVars then shareCommon (arg.instantiateRev proofs) else pure arg
  let proof := match thm.thm.expr with
    | .const declName [] => mkAppN (mkConst declName us) args
    | expr => mkAppN (expr.instantiateLevelParams thm.thm.pattern.levelParams us) args
  let rhs ← share (thm.thm.rhs.instantiateLevelParams thm.thm.pattern.levelParams us)
  let expr ← instantiateRevBetaS rhs args
  if isSameExpr e expr then return mkRflResultCD isCD
  if thm.thm.perm && !(← acLt expr e) then return mkRflResultCD isCD
  let used := if state.used.contains thm then state.used else state.used.push thm
  ctx.ref.set { goals := state.goals ++ newGoals, byType, used }
  return .step expr proof (contextDependent := isCD)

/-- Rewrites `e` with the first rule of `thms` which applies. This is
`Lean.Meta.Sym.Simp.Theorems.rewrite`, with side goals. -/
def SideGoalTheorems.rewrite (thms : SideGoalTheorems) (ctx : SideGoalContext) : Simproc :=
  fun e ↦ do
    let mut anyCD := false
    for (thm, numExtra) in getMatchWithExtra (← getMCtx) thms.thms e do
      let result ← if numExtra == 0 then
        thm.rewrite ctx e
      else
        simpOverApplied e numExtra (thm.rewrite ctx ·)
      anyCD := anyCD || result.isContextDependent
      if !result.isRfl then
        return if anyCD then result.withContextDependent else result
    return mkRflResultCD anyCD

/-- Simplifies the goal `goal` bottom-up with the rules `thms`, discharging their hypotheses with
`disch` and turning those it does not prove into side goals, when they are marked as such. Returns
the simplified goal, if it is not closed, and the side goals together with the rules used. Fails if
no progress is made. -/
def simpGoalWithSideGoals (goal : MVarId) (thms : SideGoalTheorems)
    (disch : Discharger := dischargeAssumption) : MetaM (Option MVarId × SideGoals) :=
  SymM.run do
    let goal ← preprocessMVar goal
    goal.withContext do
      let ref ← IO.mkRef ({} : SideGoals)
      let decl ← goal.getDecl
      let ctx := { lctx := decl.lctx, localInsts := decl.localInstances, disch, ref }
      let result ← simpGoal goal { post := thms.rewrite ctx }
      let sides ← ref.get
      match result with
      | .noProgress => throwError "simplification with side goals made no progress"
      | .closed => return (none, sides)
      | .goal goal => return (some goal, sides)

/-- An environment extension storing a set of `SideGoalTheorem`s. -/
abbrev SideGoalSimpExtension := SimpleScopedEnvExtension SideGoalTheorem SideGoalTheorems

/-- The extensions registered with `registerSideGoalSimpAttr`, by attribute name. -/
initialize sideGoalSimpExtensionMapRef : IO.Ref (Std.HashMap Name SideGoalSimpExtension) ←
  IO.mkRef {}

/-- Registers an attribute `@[attrName h₁ … hₙ]` adding the tagged declaration to a new set of
`SideGoalTheorem`s, whose hypotheses `h₁ … hₙ` (all of them if there are none) become side
goals. Must be called during initialization. -/
def registerSideGoalSimpAttr (attrName : Name) (descr : String)
    (ref : Name := by exact decl_name%) : IO SideGoalSimpExtension := do
  let ext ← registerSimpleScopedEnvExtension {
    name := ref
    initial := {}
    addEntry := fun thms thm ↦ thms.insert thm }
  registerBuiltinAttribute {
    ref, descr
    name := attrName
    applicationTime := .afterCompilation
    add := fun declName stx kind ↦ MetaM.run' do
      let sideGoals := stx[1].getArgs.map (·.getId)
      ext.add (← mkSideGoalTheoremFromDecl declName sideGoals) kind
    erase := fun _ ↦ throwError "erasing `{attrName}` is not supported" }
  sideGoalSimpExtensionMapRef.modify (·.insert attrName ext)
  return ext

/-- Returns the set of `SideGoalTheorem`s of the attribute `attrName`, registered with
`registerSideGoalSimpAttr`. -/
def getSideGoalTheorems (attrName : Name) : CoreM SideGoalTheorems := do
  let some ext := (← sideGoalSimpExtensionMapRef.get)[attrName]?
    | throwError "`{attrName}` is not a set of rewrite rules with side goals"
  return ext.getState (← getEnv)

/-- `register_side_goal_simp_attr foo` registers an attribute `@[foo h₁ … hₙ]` for a set of
rewrite rules with side goals: the hypotheses `h₁ … hₙ` of the tagged declaration (all of its
propositional hypotheses if there are none) become side goals. The tagged rules are returned by
`getSideGoalTheorems` applied to the name of the attribute. -/
macro (name := registerSideGoalSimpAttrCmd) doc:(docComment)?
    "register_side_goal_simp_attr " id:ident : command => do
  let str := id.getId.toString
  let attrId := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote ((doc.map (·.getDocString)).getD s!"rewrite rules with side goals {str}")
  `($[$doc:docComment]? initialize ext : SideGoalSimpExtension ←
      registerSideGoalSimpAttr $(quote id.getId) $descr
    $[$doc:docComment]? syntax (name := $attrId:ident) $(quote str):str (ppSpace ident)* : attr)

end Mathlib.Tactic.SideGoalSimp

open Mathlib.Tactic.SideGoalSimp in
/-- The default set of rewrite rules with side goals, used by `simp_side`. `@[side_goal_simp]`
makes every propositional hypothesis of the tagged lemma a side goal, and
`@[side_goal_simp h₁ … hₙ]` only `h₁ … hₙ`. -/
register_side_goal_simp_attr side_goal_simp

public meta section

namespace Mathlib.Tactic.SideGoalSimp

open Lean Meta Elab Tactic Sym Lean.Meta.Sym.Simp

/-- A rewrite rule for `simp_side`: `h` makes all the propositional hypotheses of `h` side goals,
and `h with h₁ … hₙ` only `h₁ … hₙ`. -/
syntax simpSideLemma := ident (" with" (ppSpace colGt ident)+)?

/-- `simp_side [h₁, h₂ with h, …]` rewrites the goal bottom-up with the `@[side_goal_simp]` rules
and `h₁, h₂, …`. Their hypotheses are discharged by assumption, and those which are not become side
goals instead of preventing the rewrite: all the propositional hypotheses of `h₁`, and only `h` for
`h₂`. Side goals with the same statement are created only once, and those arising under a binder `x`
are quantified over `x`.

* `simp_side only [...]` does not use the `@[side_goal_simp]` rules.
* `simp_side [...] => tac` runs `tac` on the side goals, which it must close. Without `=> tac`, it
  is an error to leave side goals.
* `simp_side?` suggests a `simp_side only` call with the rules which were used. -/
syntax (name := simpSide) "simp_side" (&" only")? (" [" withoutPosition(simpSideLemma,*,?) "]")?
  (" => " tacticSeq)? : tactic

@[inherit_doc simpSide]
syntax (name := simpSideTrace) "simp_side?" (&" only")?
  (" [" withoutPosition(simpSideLemma,*,?) "]")? (" => " tacticSeq)? : tactic

/-- Elaborates a `simp_side` rewrite rule. -/
def elabSimpSideLemma : TSyntax ``simpSideLemma → TacticM SideGoalTheorem
  | `(simpSideLemma| $id:ident $[with $hs*]?) => do
    let sideGoals := (hs.getD #[]).map (·.getId)
    if let some decl := (← getLCtx).findFromUserName? id.getId then
      mkSideGoalTheoremFromExpr decl.toExpr sideGoals
    else
      mkSideGoalTheoremFromDecl (← realizeGlobalConstNoOverloadWithInfo id) sideGoals
  | _ => throwUnsupportedSyntax

/-- The `simp_side` rewrite rule which gives back `thm`. -/
def SideGoalTheorem.toSyntax (thm : SideGoalTheorem) : MetaM (TSyntax ``simpSideLemma) := do
  let id ← match thm.thm.expr with
    | .const declName _ => pure <| mkIdent (← unresolveNameGlobalAvoidingLocals declName)
    | .fvar fvarId => pure <| mkIdent (← fvarId.getUserName)
    | e => throwError "cannot print the rewrite rule{indentExpr e}"
  if thm.sideGoals.isEmpty then
    `(simpSideLemma| $id:ident)
  else
    `(simpSideLemma| $id:ident with $(thm.sideGoals.map mkIdent)*)

/-- Runs `simp_side`, without the `@[side_goal_simp]` rules if `only` is true, with the extra
rules `lems`, and running `tac?` on the side goals if it is given (together with the `=>` token).
Returns the rules used, besides `eq_self`. -/
def evalSimpSide (only : Bool) (lems : Array (TSyntax ``simpSideLemma))
    (tac? : Option (Syntax × TSyntax ``Parser.Tactic.tacticSeq)) :
    TacticM (Array SideGoalTheorem) := do
  let mut thms ← if only then pure {} else getSideGoalTheorems `side_goal_simp
  thms := thms.insert (← mkSideGoalTheoremFromDecl ``eq_self)
  for lem in lems do
    thms := thms.insert (← elabSimpSideLemma lem)
  let (goal?, sides) ← simpGoalWithSideGoals (← getMainGoal) thms
  if let some (arrow, tac) := tac? then
    replaceMainGoal (goal?.toList ++ sides.goals.toList)
    withRef arrow <| focusGoalsAndDone sides.goals.contains (evalTactic tac)
  else
    replaceMainGoal goal?.toList
    unless sides.goals.isEmpty do
      logError m!"unsolved side goals, prove them with `simp_side ... => tac`\n\
        {goalsToMessageData sides.goals.toList}"
      sides.goals.forM (admitGoal ·)
  return sides.used.filter (!·.thm.expr.isConstOf ``eq_self)

elab_rules : tactic
  | `(tactic| simp_side $[only%$only?]? $[[$lems?,*]]? $[=>%$arrow? $tac?]?) => do
    let tac? := arrow?.bind fun arrow ↦ tac?.map (arrow, ·)
    discard <| evalSimpSide only?.isSome ((lems?.map (·.getElems)).getD #[]) tac?
  | `(tactic| simp_side? $[only%$only?]? $[[$lems?,*]]? $[=>%$arrow? $tac?]?) => do
    let stx ← getRef
    let used ← evalSimpSide only?.isSome ((lems?.map (·.getElems)).getD #[])
      (arrow?.bind fun arrow ↦ tac?.map (arrow, ·))
    let lems ← used.mapM fun thm ↦ thm.toSyntax
    let suggestion ← match tac? with
      | some tac => `(tactic| simp_side only [$lems,*] => $tac)
      | none => `(tactic| simp_side only [$lems,*])
    TryThis.addSuggestion stx suggestion (origSpan? := stx)

end Mathlib.Tactic.SideGoalSimp
