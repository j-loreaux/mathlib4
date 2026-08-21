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

/-- Elaborate the configuration of `cfc_pull`. `discharger` is omitted because its value is a
tactic rather than a term; `mkConfig` fills it in from the `(disch := ..)` clause. -/
declare_config_elab elabCFCPullConfig Config where
  omit discharger

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

/-- The auto-param tactic that the continuous functional calculus API itself would use for a
hypothesis of this kind.

`.other` gets the predicate tactic too. Its classification is deliberately coarse (see
`SideGoalKind.ofType`), so a goal landing there is often a predicate goal in disguise: `0 ≤ a * a`
is the predicate of the calculus over `ℝ≥0`, but is not recognised as one. -/
def SideGoalKind.tactic : SideGoalKind → MetaM (TSyntax `tactic)
  | .continuity => `(tactic| cfc_cont_tac)
  | .mapZero => `(tactic| cfc_zero_tac)
  | .predicate | .other =>
    -- `cfc_predicate` closes the predicate goals for the inner element of a composition, e.g.
    -- `p (cfc g a)`; the identifiers are built unresolved so that they are looked up in the
    -- user's environment rather than in this file's.  Note that `cfc_tac` never fails, so it
    -- has to come last.
    `(tactic| first
      | exact $(mkIdent `cfc_predicate) _ _
      | exact $(mkIdent `cfcₙ_predicate) _ _
      | cfc_tac)

/-- Try to close the side goals raised by the pull: `assumption` first, then the auto-param
tactic for the goal's kind, and finally — for the goals the calculus API has no auto-param for —
`cfg.discharger`. Duplicates are merged, which matters because the two sides of a relation are
pulled independently and so tend to ask for the same predicate twice.

Whatever survives is an error unless `+defer` was given, in which case it is returned to be added
to the goal list. -/
def postProcessSideGoals (cfg : Config) (goals : Array MVarId) : TacticM (Array MVarId) := do
  let mut out := #[]
  for g in goals do
    if ← g.isAssigned then continue
    let type ← instantiateMVars (← g.getType)
    -- merge with an earlier goal of the same type
    if ← out.anyM fun g' => do
        if ← withReducible <| isDefEq type (← g'.getType) then
          g.assign (mkMVar g'); return true
        else return false then
      trace[Tactic.cfc_pull] "side goal `{type}` is a duplicate"
      continue
    if ← g.assumptionCore then
      trace[Tactic.cfc_pull] "{checkEmoji} closed `{type}` with `assumption`"
      continue
    let kind := SideGoalKind.ofTag (← g.getTag)
    let tac ← kind.tactic
    if ← tryTacticOn g tac then
      trace[Tactic.cfc_pull] "{checkEmoji} closed `{type}` with `{tac}`"
      continue
    /- The user's discharger is the last resort, and only for `.other`: the hypotheses peculiar
    to an individual `@[cfc_pull]` lemma, which the calculus API has no tactic for. It is run
    separately rather than appended to `kind.tactic` with `first`, because that tactic ends in
    `cfc_tac`, which never fails and so would swallow the alternative. -/
    if kind == .other then
      if let some disch := cfg.discharger then
        if ← tryTacticOn g disch then
          trace[Tactic.cfc_pull] "{checkEmoji} closed `{type}` with the discharger `{disch}`"
          continue
    trace[Tactic.cfc_pull] "{crossEmoji} could not close `{type}`"
    out := out.push g
  unless cfg.defer || out.isEmpty do
    throwError "`cfc_pull` rewrote the goal but could not discharge \
      {out.size} side goal{if out.size == 1 then "" else "s"}:\
      {indentD (goalsToMessageData out.toList)}\n\
      Use `cfc_pull +defer ..` to have them added to the goal list instead."
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
  throwError "`cfc_pull` could not find an application of `cfc` or `cfcₙ` in the goal from\n\
    which to read off the scalar ring and the element; supply them explicitly, as in\n\
    `cfc_pull ℝ a`"

/-! ### The tactic -/

/-- Pull every argument of the target that lives in the algebra, and replace the goal by the
result. Returns the new goal (unless it was closed by `rfl`) and the surviving side goals. -/
def cfcPullTarget (cfg : Config) (R elem : Expr) (goal : MVarId) : TacticM Unit := do
  let alg ← inferType elem
  -- `consumeMData` is not optional: a goal type routinely arrives wrapped in an
  -- `mdata noImplicitLambda` annotation left by the elaborator, and `Expr.getAppArgs` does not
  -- see through `mdata`, so `targetPositions` below would find no arguments at all.
  let target := (← instantiateMVars (← goal.getType)).consumeMData
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
    -- `mkCongr` one position at a time: from `hᵢ : xᵢ = yᵢ`, folding it over `rfl : F = F`
    -- gives `F x₀ ⋯ xₙ = F y₀ ⋯ yₙ`. `F` is non-dependent by construction.
    proofs.foldlM (init := ← mkEqRefl F) fun h h' => mkCongr h h'
  let hcongr ← mkExpectedTypeHint hcongr (← mkEq target newTarget)
  let newGoal ← goal.replaceTargetEq newTarget hcongr
  let mut main := [newGoal]
  if ← tryTacticOn newGoal (← `(tactic| rfl)) then
    main := []
  replaceMainGoal (main ++ (← postProcessSideGoals cfg sideGoals).toList)

/-- Elaborate the optional scalar ring and element arguments, falling back to reading them off
the goal. `preferUnital` reports whether the calculus found in the goal (if any) was unital, so
that `cfc_pull` on a goal mentioning `cfcₙ` defaults to the non-unital calculus. -/
def elabRingAndElem (target : Expr) (ring? elem? : Option Term) :
    TacticM (Expr × Expr × Option Bool) := do
  /- The first explicit argument is the scalar ring.  Elaborating the element there is a natural
  mistake, so it gets a message of its own. -/
  let elabRing (r : Term) : TacticM Expr := do
    try
      Term.elabType r
    catch ex =>
      throwError "`cfc_pull`'s first argument is the scalar ring, but `{r}` did not elaborate \
        as a type:{indentD ex.toMessageData}\nIf `{r}` is the element to pull towards, give the \
        scalar ring as well, as in `cfc_pull ℝ {r}`."
  match ring?, elem? with
  | some r, some a =>
    let R ← elabRing r
    let elem ← Term.elabTerm a none
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars R, ← instantiateMVars elem, none)
  | some r, none =>
    let R ← elabRing r
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

The lemmas used along the way have hypotheses — continuity of the functions on the spectrum,
`f 0 = 0` in the non-unital case, and the predicate `p a` — and `cfc_pull` discharges them with
`assumption` and then with the auto-param tactic the calculus API itself uses (`cfc_cont_tac`,
`cfc_zero_tac`, `cfc_tac`). Anything left over is an error; `+defer` turns those into goals
instead, named after what they are, so that they can be addressed in groups:

```lean
example (ha : IsStrictlyPositive a) :
    CFC.log a * CFC.log a = cfc (fun x : ℝ ↦ Real.log x * Real.log x) a := by
  cfc_pull +defer ℝ a
  case cfc_pull.continuity => exact Real.continuousOn_log.mono fun x hx h ↦ ...
```

Configuration:

* `+unital` / `-unital` (default `+unital`): prefer the unital calculus `cfc`, or force the
  non-unital `cfcₙ`. With `+unital` the tactic falls back to `cfcₙ` in an algebra with no unital
  functional calculus.
* `+defer`: return the side goals that could not be discharged instead of failing.
* `(disch := tac)`: run `tac` on side goals that none of the above closed. Only the goals tagged
  `cfc_pull.side` reach it — the hypotheses peculiar to an individual `@[cfc_pull]` lemma, for
  which the calculus API has no auto-param tactic. As in `simp`, the default does nothing.
* `(maxDepth := n)`: the recursion depth limit.

In `conv` mode, `cfc_pull` acts on the current `conv` target, which is the way to pull at a
specific position:

```lean
example : star a * a + b = cfc (fun x : R ↦ star x * x) a + b := by
  conv_lhs => cfc_pull R a
```

A `conv` block cannot end with unsolved goals — the same restriction that `rw` inside `conv` is
subject to — so `+defer` is of no use there.

Going under a binder is `conv`'s job rather than the tactic's, which makes sums and the like a
two-step affair:

```lean
example : ∑ i ∈ s, star (cfc (g i) a) = cfc (∑ i ∈ s, fun x ↦ star (g i x)) a := by
  conv_lhs => enter [2, i]; cfc_pull R a
  cfc_pull R a
```

The lemmas the tactic uses are those tagged `@[cfc_pull]`; `set_option trace.Tactic.cfc_pull
true` shows which were tried and why they failed.
-/
syntax (name := cfcPull) "cfc_pull"
  -- The config parser has to be `Lean.Parser.Tactic.optConfig`, not the
  -- `Lean.Parser.Term.optConfig` that `open Lean` puts in scope: only the former excludes
  -- `disch`/`discharger` from the identifiers its `valConfigItem` accepts, and so only it
  -- leaves the clause that follows to be parsed. With the other one the configuration swallows
  -- `(disch := ..)` and reports it as an unknown configuration option.
  Lean.Parser.Tactic.optConfig (Lean.Parser.Tactic.discharger)?
  (ppSpace colGt term:max)? (ppSpace colGt term:max)? : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullConv) "cfc_pull"
  Lean.Parser.Tactic.optConfig (Lean.Parser.Tactic.discharger)?
  (ppSpace colGt term:max)? (ppSpace colGt term:max)? : conv

/-- Whether the user explicitly mentioned the configuration field `field`. -/
def configMentions (stx : Syntax) (field : Name) : Bool :=
  (stx.find? fun s => s.isIdent && s.getId == field).isSome

/-- Read the configuration, taking into account the unitality of a calculus found in the goal
when the user did not mention `unital` explicitly, and the `(disch := ..)` clause, which
`elabCFCPullConfig` cannot see. -/
def mkConfig (cfgStx : TSyntax ``Lean.Parser.Tactic.optConfig)
    (disch? : Option (TSyntax ``Lean.Parser.Tactic.discharger)) (goalUnital : Option Bool) :
    TacticM Config := do
  let mut cfg ← elabCFCPullConfig cfgStx
  if !configMentions cfgStx `unital then
    if let some u := goalUnital then
      cfg := { cfg with unital := u }
  if let some disch := disch? then
    -- the keyword is `patternIgnore`d in the parser, so it does not appear in the tree
    let `(Lean.Parser.Tactic.discharger| ($_ := $tac)) := disch | throwUnsupportedSyntax
    -- parenthesised so that a multi-tactic sequence stays one tactic
    cfg := { cfg with discharger := some (← `(tactic| ($tac))) }
  return cfg

/-- Elaborator for the `cfc_pull` tactic. -/
@[tactic cfcPull]
def evalCFCPull : Tactic := fun stx => withMainContext do
  let `(tactic| cfc_pull $cfg:optConfig $[$disch?]? $[$ring?]? $[$elem?]?) := stx
    | throwUnsupportedSyntax
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let (R, elem, goalUnital) ← elabRingAndElem target ring? elem?
  cfcPullTarget (← mkConfig cfg disch? goalUnital) R elem goal

/-- Elaborator for `cfc_pull` in `conv` mode. -/
@[tactic cfcPullConv]
def evalCFCPullConv : Tactic := fun stx => withMainContext do
  let `(conv| cfc_pull $cfg:optConfig $[$disch?]? $[$ring?]? $[$elem?]?) := stx
    | throwUnsupportedSyntax
  let lhs := (← Conv.getLhs).consumeMData
  let (R, elem, goalUnital) ← elabRingAndElem lhs ring? elem?
  let cfg ← mkConfig cfg disch? goalUnital
  let (newLhs, proof, sideGoals) ← runPull cfg R elem lhs
  Conv.updateLhs newLhs proof
  let sideGoals ← postProcessSideGoals cfg sideGoals
  replaceMainGoal ((← getGoals) ++ sideGoals.toList)

end Mathlib.Tactic.CFCPull
