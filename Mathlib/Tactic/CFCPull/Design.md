# Implementation plan for `cfc_pull`

Companion to `Spec.md`, which is the normative description of *what* the tactic does. This
document records *how* it is built: the file layout, the data structures, and the handful of
metaprogramming techniques that do the real work.

## 1. File layout

```
Mathlib/Tactic/CFCPull/Attr.lean       -- ring keys, lemma categories, env extensions, @[cfc_pull]
Mathlib/Tactic/CFCPull/Core.lean       -- PullM, the recursion (pure MetaM)
Mathlib/Tactic/CFCPull/Frontend.lean   -- syntax, tactic and conv elaborators
Mathlib/Tactic/CFCPull/Lemmas.lean     -- `attribute [cfc_pull] ...` for the Mathlib lemma set
Mathlib/Tactic/CFCPull.lean            -- imports the above
```

`Attr.lean` depends only on `Mathlib.Init` and `Lean.Meta`, so that in a final PR the
`@[cfc_pull]` tags can migrate to the declaration sites in `Mathlib/Analysis/...`. Until then
`Lemmas.lean` collects them in one place, which keeps the diff surveyable at the cost of an
unusual `Tactic → Analysis` import. `Lemmas.lean` is also where the handful of missing `rfl`
lemmas (`CFC.sqrt_def`, `CFC.abs_def`, `CFC.log_def`) live for now.

## 2. Core data structures (`Attr.lean`)

```lean
inductive RingKey | const (n : Name) | any

/-- Which calculus we are producing.  The element is fixed for a whole run and lives in the
`Context`, so a `Mode` only records the ring and the unitality.  `RingKey` is the static
approximation of `ring` stored in the index. -/
structure Mode where
  ring   : Expr
  unital : Bool

/-- The arguments of a `cfc`/`cfcₙ` application. -/
structure CFCApp where
  unital : Bool
  R A p f a : Expr
```

`CFCApp.match? : Expr → Option CFCApp` recognises `@cfc R A p _ .. _ f a` and
`@cfcₙ R A p _ .. _ f a` positionally: `R`, `A`, `p` are arguments 0, 1, 2 and `f`, `a` are the
last two, for both constants (verified: `cfc` takes 15 arguments, `cfcₙ` takes 18).

Lemma records:

```lean
structure PullLemma where
  declName : Name; symm : Bool; prio : Nat
  ring : RingKey; unital : Bool
  cfcOnLhs : Bool          -- after applying `symm`
  numHoles : Nat

structure IdLemma    where declName : Name; symm : Bool; ring : RingKey; unital : Bool
structure ScalarLemma where declName : Name; symm : Bool; src tgt : RingKey; unital : Bool
structure UnitalLemma where declName : Name; symm : Bool; ring : RingKey; nonUnitalOnLhs : Bool
structure ComposeLemma where
  declName : Name; symm : Bool; ring : RingKey; unital : Bool
  srcOnLhs : Bool          -- which side has the structured element
  innerHead : Name         -- head symbol of that element
```

Five environment extensions (`SimpleScopedEnvExtension`, mirroring `Mathlib/Tactic/Push/Attr.lean`):
a `DiscrTree PullLemma`, and four plain arrays for the other categories (they are small: a
handful of entries each, and `Id`/`Unital`/`Scalar` are looked up by mode rather than by
pattern).

### Classification at tagging time

`forallMetaTelescope` the lemma type, rather than `forallTelescope`. This matters twice over:
type and instance arguments become metavariables and are therefore indexed as `DiscrTree`
wildcards (with `forallTelescope` they would be free variables and would be indexed as such,
so no lemma would ever match), and "a variable of the lemma" becomes "an unassigned
metavariable", which is exactly what the tactic sees when it later applies the lemma. Then
`type.eq?`, apply `symm` if `←` was given, and dispatch on `CFCApp.match?` of the two sides as
the table in `Spec.md` §5 prescribes.

`RingKey` of an expression `R`: `.const n` if `R`'s head is the constant `n`, `.any` otherwise
(in particular when `R` is one of the telescope's metavariables).

Holes of a `Pull` lemma's algebra side (`abstractHoles` + `isHoleFor`): the maximal subterms `s`
such that `CFCApp.match? s` succeeds with the same unitality as the cfc side, the same ring and
element up to `withNewMCtxDepth`-guarded `isDefEq`, and a *variable* function argument. Reject
the lemma if any hole contains a loose bound variable (see `Spec.md` §11). The `DiscrTree` key is
`DiscrTree.mkPath` of the algebra side with holes replaced by fresh metavariables.

The same `abstractHoles`/`isHoleFor` pair runs again at application time, with "variable"
reinterpreted as "unassigned metavariable"; this is why the hole notion is parameterised by a
predicate rather than hard-coded.

## 3. The recursion (`Core.lean`)

```lean
structure Context where
  cfg      : Config
  elem     : Expr          -- `a`
  alg      : Expr          -- `A`
  ring     : Expr          -- the *target* ring `R`
  unital   : Bool          -- the *target* unitality
  depth    : Nat

structure State where
  sideGoals : Array MVarId
  /-- cache: mode ↦ (predicate, instance, shared `?ha : p a`) -/
  predicates : Array (Expr × Bool × Expr × Expr)

abbrev PullM := ReaderT Context (StateRefT State MetaM)

structure Result where
  mode  : Mode
  fn    : Expr             -- `f : mode.ring → mode.ring`
  rhs   : Expr             -- `cfc f a`, kept verbatim so its instances are the lemma's
  proof : Expr             -- `e = rhs`
```

The entry points are

```lean
partial def pull           (e : Expr) (want : Mode) : PullM Result   -- guaranteed at `want`
partial def pullExisting   (e : Expr) (c : CFCApp) (want : Mode) : PullM Result
partial def pullCandidates (e : Expr) (want : Mode) : PullM (Array PullLemma)
def convert (r : Result) (want : Mode) : PullM Result
def runPull (cfg : Config) (R elem e : Expr) : MetaM (Expr × Expr × Array MVarId)
```

and the workers that apply a single tagged lemma:

```lean
def applyPullLemma      (l : PullLemma) (e : Expr) (want : Mode)
                        (rec : Expr → Mode → PullM Result) : PullM Result
def applyLooseLemma     (l : PullLemma) (e : Expr) (want : Mode) : PullM (Expr × Expr)
def rewriteWithCFCLemma (declName : Name) (symm srcOnLhs : Bool) (e : Expr) (mode : Mode) :
                          PullM (Expr × Expr)
def applyTransition     (declName : Name) (symm srcOnLhs : Bool) (res : Result) : PullM Result
```

`rewriteWithCFCLemma` turned out to cover the `Scalar`, `Unital` *and* `Compose` categories at
once: all three are equations between two applications of the calculus, and matching one side
against `e` determines the ring, the predicate, the function and the element in one go. The
three categories differ only in which of those the two sides disagree about, which the caller
already knows and the routine does not need to.

### Applying a `Pull` lemma — the central routine

This is the only genuinely delicate piece. Given the target `e` and a candidate:

1. `forallMetaTelescope` the lemma type; keep the `BinderInfo` array.
2. Split into cfc side / algebra side according to `cfcOnLhs`.
3. `isDefEq` the cfc side's `A`, `R`, `p`, element against ours. Order matters: doing the
   element **before** the pattern match is what pins down lemmas whose algebra side does not
   mention the element.
4. For every instance-implicit metavariable still unassigned, `synthInstance` and assign.
   Rejection here is the mechanism that filters `CommRing`/`RCLike`/`UniqueHom` requirements.
5. Recompute the holes on the *instantiated* algebra side and build the pattern by substituting
   a fresh natural metavariable `?xᵢ : A` for each. **Save the pre-unification pattern.**
6. `withReducible <| isDefEq pattern e`.
7. Recurse on each `instantiateMVars ?xᵢ` at the lemma's mode.
8. `isDefEq` each lemma function variable against the recursively produced function.
9. Discharge/collect the remaining metavariables (§4).
10. Build the proof (§3.1) and β-reduce.

### 3.1 Building the congruence proof

After step 8 we have, for each hole, `pᵢ : xᵢ = cfc fᵢ a`, and we need
`e = ⟨algebra side⟩`. The trick is to abstract the holes into a genuine function:

```lean
withLocalDeclsD (holes.map fun _ => (`x, fun _ => pure A)) fun xs => do
  -- `patSaved` still mentions the hole metavariables *syntactically*, because `Expr` is
  -- immutable; `Expr.replace` swaps them for the fvars before `instantiateMVars` fills in
  -- everything else.
  let body ← instantiateMVars <| patSaved.replace fun
    | .mvar m => (holeIdx m).map (xs[·]!)
    | _       => none
  let F ← mkLambdaFVars xs body                  -- `A → ⋯ → A → A`, non-dependent
```

and then fold `mkCongr` starting from `Eq.refl F`:

```lean
hcongr : F x₁ ⋯ xₙ = F (cfc f₁ a) ⋯ (cfc fₙ a)
```

Both sides are β-redexes; `mkExpectedTypeHint` retypes the result as `e = ⟨algebra side⟩` (β is
defeq at any transparency, and the left-hand side is `e` up to the reducible unification of
step 6). Finally `mkEqTrans hcongr (← mkEqSymm lemmaInstance)` — or without the `symm` when the
algebra side is on the left.

The zero-hole case degenerates to `hcongr := rfl`, so no special casing is needed.

### 3.2 Backtracking

Every candidate is tried inside

```lean
def observing (x : PullM α) : PullM (Option α) := do
  let sMeta ← Meta.saveState; let sPull ← get
  try pure (some (← x))
  catch _ => sMeta.restore; set sPull; pure none
```

so that a failed candidate leaves neither metavariable assignments nor stray side goals behind.
Side goals are stored in `State`, hence covered by the same checkpoint.

### 3.3 Side goals

`forallMetaTelescope` produces metavariables whose types may be `autoParam T tac`. Before a
metavariable becomes a goal its type is passed through `consumeAutoParam` so the user sees `T`.
For each undischarged metavariable in order:

1. if its type is defeq to `p a` for the lemma's mode, assign the cached shared `?ha`;
2. otherwise convert it to a synthetic-opaque metavariable and push it onto `State.sideGoals`.

(Natural metavariables cannot be returned as goals directly; the routine creates a fresh
synthetic-opaque one of the same type and assigns the natural one to it.)

## 4. Frontend (`Frontend.lean`)

```lean
structure Config where
  unital    : Bool := true    -- prefer the unital calculus
  discharge : Bool := false   -- run cfc_tac/cfc_cont_tac/cfc_zero_tac on side goals
  maxDepth  : Nat  := 48
declare_config_elab elabConfig Config
```

`Option Bool` cannot be used with `+flag`/`-flag` syntax (Lean rejects non-boolean fields), so
`unital` is a plain `Bool` read as "*prefer* unital", with automatic fallback to `cfcₙ` when no
unital instance exists. This gives the same expressiveness with standard syntax.

Tactic mode:

* infer `R`/`a` if absent by scanning the goal for a `CFCApp`, right-hand side first;
* find the arguments of the target to pull on: the target is `mkAppN rel args`; take the trailing
  arguments whose type is `A` (at most two);
* run `pull` on each, tolerating individual failures;
* rebuild the target with `mkCongr`/`mkCongrArg` over the relation, close the old goal with
  `mkEqMPR`, and `try rfl` on the new one;
* post-process side goals (`assumption`, then optionally the auto-param tactics), and
  `setGoals` with what survives, main goal first.

Conv mode: `Conv.getLhs`, run `pull`, `Conv.updateLhs newLhs proof`, then append the side goals.

## 4a. Two things the first design got wrong

Both were found by running the examples, and both are worth remembering.

**Instances are not a problem.** The worry was that matching a lemma's algebraic side at
reducible transparency would fail on the instance arguments, since e.g. `cfc_mul`'s pattern
carries `Distrib.toMul (instDistribOfSemiring (Ring.toSemiring ?instRing))` — a projection chain
stuck on a metavariable — where the goal carries a concrete chain through `CStarAlgebra`. In
fact `isDefEq` resolves this without help (it synthesises instance metavariables when it gets
stuck on them), so no instances need to be synthesised before matching, at reducible
transparency or otherwise. Instances are synthesised *after* the match, which is also what makes
"this lemma does not apply over `ℝ≥0`" fall out for free.

**`mkAppM` cannot build a class application.** `mkAppM ``ContinuousFunctionalCalculus #[R, A, ?p]`
silently returns a three-argument application, because `mkAppM` stops at the last explicit
argument and this class's instance arguments come after it. `synthInstance` then fails on the
malformed type and the tactic concludes there is no functional calculus. `mkClassApp` in
`Core.lean` does the job properly, by `forallMetaTelescope`-ing the class and synthesising every
instance argument; with a well-formed type, `synthInstance` resolves the `outParam` `?p` as
expected.

## 5. Milestones

1. **`Attr.lean`** — data structures, classification, extensions, attribute. Test by tagging a
   handful of lemmas and dumping the index with a `#cfc_pull_index` command (kept as a debug aid
   behind a `set_option`, or simply as a `run_cmd` in the test file).
2. **`Core.lean` skeleton** — modes, predicate cache, `Id` and "already a `cfc`" steps, no
   lemma index. Enough to prove `a = cfc (fun x ↦ x) a` and `cfc f a = cfc f a`.
3. **`Pull` lemma application** — the routine of §3, with congruence building. Target:
   §8.1 of `Spec.md` (`star a * a`).
4. **Conversions** — `Unital` and `Scalar`, with the BFS. Target: §8.2 (`a⁺` over `ℂ`).
5. **Composition** — step 2 of the algorithm plus the `Compose` index. Target: §8.3.
6. **Frontend polish** — inference of `R`/`a`, conv mode, `+discharge`, tracing.
7. **Lemma tagging** — work through `Spec.md` §9 and `Examples.lean`, fixing what breaks.

Each milestone is a commit; `Examples.lean` is the running test suite and is kept compiling
throughout.

## 6. Status

All of the above is implemented, and every example in `Examples.lean` compiles with no `sorry`.
Two refinements were added on top of the plan once the examples were running:

* **Step 3b of the algorithm** (`applyLooseLemma`): a hole-free pull lemma may be applied at an
  element other than the one being pulled towards, after which the algorithm re-enters and
  handles the mismatch as a composition. Without it `NormedSpace.exp (I • a)` is stuck, because
  `CFC.complex_exp_eq_normedSpace_exp` only ever matches `NormedSpace.exp a` itself.
* **Unitality before composition** (in `pullExisting`): when the outer calculus is `cfcₙ` and the
  unital one was requested, `cfcₙ_eq_cfc` is applied to the whole expression before descending
  into the inner element. Otherwise the inner expression is pulled in the non-unital calculus and
  every constant in it acquires an unprovable `f 0 = 0` side goal.

Remaining loose ends, in rough priority order:

1. `Examples.lean` imports all of Mathlib, so it is not registered in `Mathlib.lean` (the four
   tactic files are). It should become `MathlibTest/CFCPull.lean`.
2. The `@[cfc_pull]` tags in `Lemmas.lean` should move to the declaration sites, and the three
   `rfl` lemmas it adds (`CFC.sqrt_def`, `CFC.abs_def`, `CFC.log_def`) to their natural homes.
3. The scalar-ring choice is greedy (see `Spec.md` §11).
