/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Tactic.CFCPull.Core
public meta import Lean.Elab.Tactic.Conv.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# The `cfc_pull` tactic

The user-facing side of `cfc_pull`: syntax, elaboration of the scalar ring and the element,
locating the subterms of the goal to rewrite, and post-processing the side goals.

See `Mathlib/Tactic/CFCPull/Spec.md` for the specification.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta Elab Tactic

declare_config_elab elabCFCPullConfig Config

/-! ### Side goals -/

/-- Run a tactic on a goal, returning `true` if it closed the goal and restoring the state
otherwise. -/
def tryTacticOn (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    if (← Tactic.run g (evalTactic tac)).isEmpty then
      return true
  catch _ => pure ()
  s.restore
  return false

/-- The auto-param tactic appropriate to a side goal: `cfc_cont_tac` for continuity goals,
`cfc_zero_tac` for goals of the form `f 0 = 0`, and `cfc_tac` for everything else (in practice,
for the predicate `p a`). -/
def autoParamTacticFor (g : MVarId) : MetaM (TSyntax `tactic) := do
  let type ← whnfR (← g.getType)
  if type.isAppOf `ContinuousOn then
    `(tactic| cfc_cont_tac)
  else if type.isAppOf ``Eq then
    `(tactic| cfc_zero_tac)
  else
    -- `cfc_predicate` closes the predicate goals for the inner element of a composition, e.g.
    -- `p (cfc g a)`; the identifiers are built unresolved so that they are looked up in the
    -- user's environment rather than in this file's.
    -- note that `cfc_tac` never fails, so it has to come last
    `(tactic| first
      | exact $(mkIdent `cfc_predicate) _ _
      | exact $(mkIdent `cfcₙ_predicate) _ _
      | cfc_tac)

/-- Try to close the collected side goals: `assumption` always, and the standard auto-param
tactics when `+discharge` was given. Duplicates are merged, which matters because the two sides
of a relation are pulled independently and so tend to ask for the same predicate twice. Returns
the goals that survive. -/
def postProcessSideGoals (cfg : Config) (goals : Array MVarId) : TacticM (Array MVarId) := do
  let mut out := #[]
  for g in goals do
    if ← g.isAssigned then continue
    -- merge with an earlier goal of the same type
    let type ← instantiateMVars (← g.getType)
    if ← out.anyM fun g' => do
        if ← withReducible <| isDefEq type (← g'.getType) then
          g.assign (mkMVar g'); return true
        else return false then
      continue
    if ← g.assumptionCore then continue
    if cfg.discharge then
      if ← tryTacticOn g (← autoParamTacticFor g) then continue
    out := out.push g
  return out

/-! ### Determining the scalar ring and the element -/

/-- Find an application of `cfc` or `cfcₙ` inside `e`, outermost first. -/
def findCFCApp? (e : Expr) : Option CFCApp := do
  let s ← e.find? fun s => (CFCApp.match? s).isSome
  CFCApp.match? s

/-- The positions in the target that `cfc_pull` should act on: those arguments of the head
application whose type is the algebra `A`. For `lhs = rhs` these are `lhs` and `rhs`; for
`lhs ≤ rhs` likewise. -/
def targetPositions (target alg : Expr) : MetaM (Array Nat) := do
  let args := target.getAppArgs
  let mut out := #[]
  for _h : i in [0:args.size] do
    if ← isDefEq (← inferType args[i]) alg then
      out := out.push i
  return out

/-- Work out the scalar ring and the element from the goal when the user did not supply them:
look for an application of the calculus, preferring the later arguments of the target (i.e. the
right-hand side of a relation). Returns the `CFCApp` found. -/
def inferCFCApp (target : Expr) : MetaM CFCApp := do
  let args := target.getAppArgs
  for i in [0:args.size] do
    let arg := args[args.size - 1 - i]!
    if let some c := findCFCApp? arg then
      return c
  if let some c := findCFCApp? target then return c
  throwError "`cfc_pull` could not find an application of `cfc` or `cfcₙ` in the goal from which \
    to read off the scalar ring and the element; supply them explicitly, as in `cfc_pull ℝ a`"

/-! ### The tactic -/

/-- Pull every argument of the target that lives in the algebra, and replace the goal by the
result. Returns the new goal (unless it was closed by `rfl`) and the surviving side goals. -/
def cfcPullTarget (cfg : Config) (R elem : Expr) (goal : MVarId) : TacticM Unit := do
  let alg ← inferType elem
  let target ← instantiateMVars (← goal.getType)
  let positions ← targetPositions target alg
  if positions.isEmpty then
    throwError "`cfc_pull` found nothing of type `{alg}` in the goal{indentExpr target}"
  let args := target.getAppArgs
  let mut newArgs := args
  let mut proofs := #[]
  let mut sideGoals := #[]
  let mut changed := false
  let mut failures : Array String := #[]
  for i in positions do
    let arg := args[i]!
    let mctx ← getMCtx
    let attempt : Except String (Expr × Expr × Array MVarId) ← (do
      try
        return .ok (← runPull cfg R elem arg)
      catch ex =>
        setMCtx mctx
        return .error (← ex.toMessageData.toString))
    match attempt with
    | .ok (newArg, proof, goals) =>
      newArgs := newArgs.set! i newArg
      proofs := proofs.push proof
      sideGoals := sideGoals ++ goals
      unless newArg == arg do changed := true
    | .error msg =>
      -- the two sides of a relation usually fail for the same reason; do not say so twice
      unless failures.contains msg do failures := failures.push msg
      proofs := proofs.push (← mkEqRefl arg)
  unless changed do
    throwError "`cfc_pull` made no progress\
      {indentD (MessageData.joinSep (failures.toList.map (m!"{·}")) m!"\n")}"
  -- Rebuild the goal by congruence over the positions we changed.
  let newTarget := mkAppN target.getAppFn newArgs
  let hcongr ← withLocalDeclsD (positions.map fun _ => (`x, fun _ => pure alg)) fun xs => do
    let mut body := args
    for _h : j in [0:positions.size] do
      body := body.set! positions[j]! xs[j]!
    let F ← mkLambdaFVars xs (mkAppN target.getAppFn body)
    mkCongrN F proofs
  let hcongr ← mkExpectedTypeHint hcongr (← mkEq target newTarget)
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newTarget (tag := ← goal.getTag)
  goal.assign (← mkEqMPR hcongr newGoal)
  let mut main := [newGoal.mvarId!]
  if ← tryTacticOn newGoal.mvarId! (← `(tactic| rfl)) then
    main := []
  replaceMainGoal (main ++ (← postProcessSideGoals cfg sideGoals).toList)

/-- Elaborate the optional scalar ring and element arguments, falling back to reading them off
the goal. `preferUnital` reports whether the calculus found in the goal (if any) was unital, so
that `cfc_pull` on a goal mentioning `cfcₙ` defaults to the non-unital calculus. -/
def elabRingAndElem (target : Expr) (ring? elem? : Option Term) :
    TacticM (Expr × Expr × Option Bool) := do
  match ring?, elem? with
  | some r, some a =>
    let R ← Term.elabType r
    let elem ← Term.elabTerm a none
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars R, ← instantiateMVars elem, none)
  | some r, none =>
    let R ← Term.elabType r
    Term.synthesizeSyntheticMVarsNoPostponing
    let c ← inferCFCApp target
    return (← instantiateMVars R, c.a, some c.unital)
  | none, some _ =>
    throwError "`cfc_pull`: the element may only be given together with the scalar ring"
  | none, none =>
    let c ← inferCFCApp target
    return (c.R, c.a, some c.unital)

/--
`cfc_pull R a` rewrites the goal so that the continuous functional calculus is at the head of
every expression in the algebra: each side of the goal is replaced by `cfc f a` (or `cfcₙ f a`)
for a function `f : R → R` that the tactic works out.

This automates the standard technique for proving identities in a C⋆-algebra: pull `cfc` to the
head on both sides, and then use `cfc_congr` to reduce to an equality of functions on the
spectrum. If both sides end up with the same function, `cfc_pull` closes the goal outright.

```lean
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a <;> fun_prop
```

Both arguments are optional: `cfc_pull` on its own reads the scalar ring and the element off an
application of `cfc`/`cfcₙ` already present in the goal, preferring the right-hand side.

The hypotheses of the lemmas used along the way (continuity of the functions on the spectrum,
`f 0 = 0` in the non-unital case, and the predicate `p a`) are returned as side goals, after the
main goal; `assumption` is tried on each of them first. Configuration:

* `+unital` / `-unital` (default `+unital`): prefer the unital calculus `cfc`, or force the
  non-unital `cfcₙ`. With `+unital` the tactic falls back to `cfcₙ` in an algebra with no unital
  functional calculus.
* `+discharge`: also try `cfc_tac`, `cfc_cont_tac` and `cfc_zero_tac` on the side goals.
* `(maxDepth := n)`: the recursion depth limit.

In `conv` mode, `cfc_pull` acts on the current `conv` target, which is the way to pull at a
specific position:

```lean
example : star a * a + b = cfc (fun x : R ↦ star x * x) a + b := by
  conv_lhs => cfc_pull R a
```

The lemmas the tactic uses are those tagged `@[cfc_pull]`; `set_option trace.Tactic.cfc_pull
true` shows which were tried and why they failed.
-/
syntax (name := cfcPull) "cfc_pull" optConfig
  (ppSpace colGt term:max)? (ppSpace colGt term:max)? : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullConv) "cfc_pull" optConfig
  (ppSpace colGt term:max)? (ppSpace colGt term:max)? : conv

/-- Whether the user explicitly mentioned the configuration field `field`. -/
def configMentions (stx : Syntax) (field : Name) : Bool :=
  (stx.find? fun s => s.isIdent && s.getId == field).isSome

/-- Read the configuration, taking into account the unitality of a calculus found in the goal
when the user did not mention `unital` explicitly. -/
def mkConfig (cfgStx : Syntax) (goalUnital : Option Bool) : TacticM Config := do
  let mut cfg ← elabCFCPullConfig cfgStx
  if !configMentions cfgStx `unital then
    if let some u := goalUnital then
      cfg := { cfg with unital := u }
  return cfg

@[tactic cfcPull]
def evalCFCPull : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (R, elem, goalUnital) ← elabRingAndElem target (stx[2].getOptional?.map (⟨·⟩))
    (stx[3].getOptional?.map (⟨·⟩))
  let cfg ← mkConfig stx[1] goalUnital
  cfcPullTarget cfg R elem goal

@[tactic cfcPullConv]
def evalCFCPullConv : Tactic := fun stx => withMainContext do
  let lhs ← Conv.getLhs
  let (R, elem, goalUnital) ← elabRingAndElem lhs (stx[2].getOptional?.map (⟨·⟩))
    (stx[3].getOptional?.map (⟨·⟩))
  let cfg ← mkConfig stx[1] goalUnital
  let (newLhs, proof, sideGoals) ← runPull cfg R elem lhs
  Conv.updateLhs newLhs proof
  let sideGoals ← postProcessSideGoals cfg sideGoals
  replaceMainGoal ((← getGoals) ++ sideGoals.toList)

end Mathlib.Tactic.CFCPull
