# Specification for the `cfc_pull` tactic

`cfc_pull` is a tactic used to automate the process of taking a term (generally in a C⋆-algebra,
but anything with a `ContinuousFunctionalCalculus` or `NonUnitalContinuousFunctionalCalculus`
instance will work) and proving (modulo some side goals collected and deferred for later) that
it is equal to another term with `cfc` (or `cfcₙ`) at the head of the expression.

This is useful for implementing a common technique for C⋆-algebras to show that two terms involving
the continuous functional calculus are equal. One first moves `cfc` to the head of the expression
within each term, and then applies `cfc_congr` to reduce the problem to showing that the
corresponding functions are equal on the spectrum.

> **Status.** This document is the *normative* specification. The companion document
> `Design.md` records the implementation plan and the metaprogramming techniques used.

## Contents

1. [The core operation](#1-the-core-operation)
2. [User-facing syntax](#2-user-facing-syntax)
3. [Scalar rings](#3-scalar-rings)
4. [Predicates](#4-predicates)
5. [The `cfc_pull` attribute](#5-the-cfc_pull-attribute)
6. [The algorithm](#6-the-algorithm)
7. [Side goals](#7-side-goals)
8. [Worked examples](#8-worked-examples)
9. [Lemmas to tag](#9-lemmas-to-tag)
10. [Errors, tracing and limits](#10-errors-tracing-and-limits)
11. [Deliberate non-goals and future work](#11-deliberate-non-goals-and-future-work)

---

## 1. The core operation

Everything in the tactic is built out of a single recursive `MetaM` operation.

> **`pull`.** Fix a *target*
> * a scalar ring `R`,
> * an element `a : A`,
> * a unitality flag `u : Bool` (`true` ⇝ `cfc`, `false` ⇝ `cfcₙ`).
>
> Call the triple `(R, a, u)` the **mode**. Given an expression `e : A`, `pull` produces a
> function `f : R → R` and a proof of
> ```
> e = cfc f a          (if u)          e = cfcₙ f a         (if ¬u)
> ```
> together with a list of *side goals* (metavariables) that the proof depends on.

Note that the direction of the equation is `e = cfc f a`: the recursion is *bottom-up* and each
step composes proofs with `Eq.trans` and congruence. There are no "output metavariables"
threaded through the recursion; the spec's original sketch (creating `?f₁`, `?hf₁`, ... and
relying on later unification to fill them in) describes the same algorithm in a more indirect
way. Returning `(f, proof)` pairs directly is equivalent, easier to reason about, and makes
backtracking straightforward.

All matching against `e` and all comparisons with `a` are done at **reducible** transparency, as
is standard for Lean tactics. In particular `cfc`, `cfcₙ`, `CFC.sqrt`, `CFC.log`, `posPart`, …
never unfold on their own: the tactic only ever "sees through" a definition when a lemma tagged
`@[cfc_pull]` tells it to.

The rest of the tactic is a thin frontend that decides *where* in the goal `pull` should be
applied and *what* the mode should be.

## 2. User-facing syntax

```
cfc_pull (config)? (R)? (a)?
```
and, in `conv` mode,
```
conv ... => cfc_pull (config)? (R)? (a)?
```

* `R` is the scalar ring, `a` the element of the algebra. Both are optional and positional; if
  `a` is omitted it must be inferrable, and if `R` is omitted both must be inferrable (you cannot
  give `a` without `R`).
* **Inference.** If either is omitted, the tactic scans the goal for a subterm of the form
  `cfc f b` or `cfcₙ f b`, preferring the right-hand side of a relation, and takes `R`/`a` from
  it. This makes `cfc_pull` alone work for the common goal shape `lhs = cfc f a`.
* **Configuration** (standard `optConfig` syntax):
  * `+unital` / `-unital` (default `+unital`). Read as *prefer* the unital calculus: with
    `+unital` the tactic uses `cfc` whenever a unital `ContinuousFunctionalCalculus R A p`
    instance exists, and silently falls back to `cfcₙ` when it does not (e.g. in a non-unital
    algebra). With `-unital` the tactic always produces `cfcₙ`.
  * `+defer` (default `false`). Return the side goals that could not be discharged instead of
    failing; see [§7](#7-side-goals).
  * `(maxDepth := n)` (default `48`), a recursion-depth guard.
* **Discharger** (the `(disch := tac)` clause of `simp` and `fun_prop`, and written after the
  configuration items as it is there). A tactic to try on side goals nothing else closed; see
  [§7](#7-side-goals). It is not an `optConfig` item, because its value is a tactic rather than
  a term, so it is a separate syntax node and `elabCFCPullConfig` omits the corresponding field.
  The default does nothing.

### Behaviour on the goal

In tactic mode, the goal must be an application `rel lhs rhs` whose last two explicit arguments
have type `A` (this covers `=`, `≤`, `<`, `≠`, …), or an application `f lhs` with a single such
argument. `pull` is run on each such argument; failures on individual arguments are tolerated as
long as at least one argument succeeds and at least one argument actually changes. The goal is
then replaced by the corresponding relation between the pulled terms, and `rfl` is attempted on
the result (which closes goals like `star a * a = cfc (fun x ↦ star x * x) a` outright).

In `conv` mode the current `conv` target is pulled, which gives the user complete control over
*where* the pull happens; this replaces the "pattern" idea in the original draft, at no cost in
expressiveness and with no new syntax to learn. Note that a `conv` block cannot end with unsolved
goals, so in `conv` mode a surviving side goal is an error and `+defer` is of no use there.
This is not specific to `cfc_pull` — `rw` inside `conv` behaves the same way.

## 3. Scalar rings

A tagged lemma's scalar ring is recorded as a **ring key**:

```lean
inductive RingKey
  | const (n : Name)   -- the lemma is about a fixed ring, e.g. `Real`, `Complex`, `NNReal`
  | any                -- the lemma is polymorphic in its scalar ring
```

`RingKey.any` covers *both* the "generic commutative (semi)ring `R`" case and the `RCLike 𝕜`
case. There is no need to distinguish them: a lemma stated for `RCLike 𝕜` simply fails instance
synthesis when the tactic tries to use it at `ℝ≥0`, and the candidate is discarded by
backtracking. The same mechanism resolves the `CommRing` vs. `CommSemiring` question raised in
the original draft (e.g. `cfc_sub` only assumes `CommRing R`): no bookkeeping is required,
instance synthesis is the arbiter.

The "ordering on scalar rings" of the original draft splits into two genuinely different notions:

* **Specialisation.** A lemma with key `any` can be used at *any* target ring, subject to
  instance synthesis. This is the `R → _` and `𝕜 → ℝ`, `𝕜 → ℂ` part of the draft's ordering.
* **Conversion.** A result *already established* over ring `S` can be moved to ring `T` by a
  `Scalar`-category lemma (see [§5](#5-the-cfc_pull-attribute)). The available conversions form a
  directed graph whose edges are exactly the tagged `Scalar` lemmas; the tactic finds a shortest
  path by breadth-first search. With the lemmas listed in [§9](#9-lemmas-to-tag) the graph is
  `ℝ≥0 → ℝ → ℂ` (in both unital and non-unital flavours), which is the draft's `ℝ≥0 → ℝ`,
  `ℝ → ℂ`. Nothing about `ℝ≥0`, `ℝ`, `ℂ` is hard-coded: the graph is whatever has been tagged.

## 4. Predicates

Attached to each scalar ring there is a predicate associated with the continuous functional
calculus. For `ℂ`, `ℝ` and `ℝ≥0` these are `IsStarNormal`, `IsSelfAdjoint` and `(0 ≤ ·)`
respectively; for a generic `R` it is a variable `p : A → Prop`.

The tactic never hard-codes these. Instead, for each mode `(R, u)` it synthesises

```lean
ContinuousFunctionalCalculus R A ?p            -- if u
NonUnitalContinuousFunctionalCalculus R A ?p   -- if ¬u
```

and reads `p` off the `outParam`. It then creates **one** metavariable `?ha : p a` per mode,
caches it, and uses it for every `p a` hypothesis of every lemma applied at that mode. So a
successful run leaves at most one `p a` goal per scalar ring used, not one per lemma
application.

## 5. The `cfc_pull` attribute

```
@[cfc_pull] @[cfc_pull ←] @[cfc_pull (prio)]
```

marks a lemma for use by the tactic. `←` uses the lemma right-to-left. Tagged lemmas must be
equations `lhs = rhs` in which at least one side has `cfc` or `cfcₙ` as its head symbol. The
attribute analyses the statement (under `forallMetaTelescopeReducing`, so that the lemma's
binders become the same metavariables the tactic will later unify against) and sorts it into one
of **five** categories. (The draft had four; the `Id` category is split off from `Pull` because
its algebra side has no head symbol to index on.)

Write `E` for the `cfc`/`cfcₙ` **element** argument and `F` for its **function** argument.

| Category | Shape | Recognised by |
|---|---|---|
| `Id`      | `cfc (fun x ↦ x) a = a` | exactly one side is a cfc-application, and the other side is exactly its element argument |
| `Pull`    | `cfc F a = ⟨algebra expression⟩` | exactly one side is a cfc-application |
| `Scalar`  | `cfc (F : S → S) a = cfc (G : T → T) a` | both sides are cfc-applications with **different** scalar rings |
| `Unital`  | `cfcₙ F a = cfc F a` | both sides are cfc-applications, same ring, **different** unitality |
| `Compose` | `cfc (fun x ↦ F (G x)) a = cfc F ⟨expression in a⟩` | both sides are cfc-applications, same ring and unitality, **different** elements |

For `Compose`, the side to rewrite *from* is the one whose element is the larger expression
(measured by node count); this is more robust than requiring the other side's element to be a bare
variable, which fails for lemmas like `cfc_comp_inv : cfc (fun x ↦ f x⁻¹) ↑a = cfc f ↑a⁻¹`.

Stored data per category:

* **`Id`** — the ring key and unitality. Indexed by `(ringKey, unital)`.
* **`Pull`** — the ring key, the unitality, which side carries the `cfc`, the number of
  *holes* (see below) and a `DiscrTree` key computed from the algebra side. Indexed by that
  `DiscrTree`.

  A **hole** is a maximal subterm of the algebra side which is itself a `cfc`/`cfcₙ` application
  at the same ring, unitality and element as the cfc side, and whose function argument is a
  variable bound by the lemma. In `cfc_mul : cfc (fun x ↦ f x * g x) a = cfc f a * cfc g a` the
  holes are `cfc f a` and `cfc g a`; in `cfc_pow_id : cfc (· ^ n) a = a ^ n` there are none. The
  `DiscrTree` key is computed after replacing the holes by wildcards, so `cfc_mul` is indexed
  under `HMul.hMul _ _ _ _ * *`.

  A hole may sit under a binder, but it may not *mention* the bound variable: in
  `cfc_sum : cfc (∑ i ∈ s, f i) a = ∑ i ∈ s, cfc (f i) a` the subterm `cfc (f i) a` mentions `i`
  and so is not recognised as a hole. Such a lemma is still tagged — with one fewer hole, and a
  warning saying so — and remains usable in the degenerate case where that position is *already*
  an application of the calculus (higher-order pattern unification solves `cfc (?f i) a` against
  `cfc (g i) a`). What it cannot do is recurse into the summands: `cfc_pull` gets stuck on
  `∑ i ∈ s, star (cfc (g i) a)`. See [§11](#11-deliberate-non-goals-and-future-work) for what
  supporting this properly would take.
* **`Scalar`** — source ring key, target ring key, unitality. Stored as an edge list.
* **`Unital`** — the ring key and which side is non-unital. Stored as a list; usable in both
  directions (right-to-left needs no extra hypotheses beyond those of the lemma).
* **`Compose`** — the ring key, the unitality, and the head symbol of the *structured* element,
  i.e. of the element argument on the source side. For `cfc_comp'` the head symbol is `cfc`
  itself; for `cfc_comp_pow` it is `HPow.hPow`. Indexed by head symbol.

Tagging a lemma that does not fit any category is an error, and the error message says why.

## 6. The algorithm

### 6.1 Setup (frontend)

0. Elaborate `R` and `a`, or infer them from the goal. Set `A := ` the type of `a`.
1. Determine unitality: with `+unital`, synthesise `ContinuousFunctionalCalculus R A ?p`; if it
   fails, fall back to non-unital. With `-unital`, go straight to non-unital.
2. Read the predicate `p` off the instance and allocate the shared `?ha : p a` metavariable.
3. Locate the arguments of the goal to be pulled (§2), and call `pull` on each.

### 6.2 `pull mode e`

The steps are tried in order; the first that succeeds wins, and any step may be undone by
backtracking (the `MetaM` state is checkpointed around every candidate).

1. **Identity.** If `e` and `a` are defeq at reducible transparency, use the `Id` lemma for
   `mode` (or for a mode convertible to `mode`; see step 5). Result: `f := fun x ↦ x`.

   This *must* be tried first: `a` may itself be e.g. `star b * b`, and decomposing it would be
   wrong.

2. **Existing calculus.** If `e` is `cfc g b` or `cfcₙ g b` — say at mode `m'` — then:
   * if `b` is defeq to `a`: the result is `(g, rfl)` at mode `m'`; go to step 5.
   * otherwise this is a **composition**, handled in three stages.
     * First, if `m'` and `mode` disagree about unitality, apply the `Unital` lemma to `e`
       *before* descending into `b`. Composing in the non-unital calculus when the unital one was
       requested would put a spurious `f 0 = 0` side goal on every piece of `b` — this is the
       difference between `cfcₙ Real.sqrt (1 - a ^ 2)` generating the unprovable goal
       `(1 : ℝ) = 0` and generating nothing at all.
     * Then, if a `Compose` lemma for `(m', head of b)` matches, apply it. This rewrites
       `cfc g b` to `cfc g' b'` with `b'` a subterm of `b`, and the algorithm recurses on the
       result. (E.g. `cfc f (a ^ n)` ⇝ `cfc (fun x ↦ f (x ^ n)) a` via `cfc_comp_pow`.)
     * Otherwise, recurse on `b` at mode `m'`, obtaining `b = cfc h a`, use `congrArg` to get
       `cfc g b = cfc g (cfc h a)`, and re-enter the algorithm, which now finds the `Compose`
       lemma whose head symbol is `cfc` (i.e. `cfc_comp'`). This requires a `UniqueHom`
       instance.

3. **Tagged pull lemmas.** Look up the head of `e` in the `Pull` index and try the candidates in
   order of preference:
   1. lemmas whose mode is exactly `mode`;
   2. lemmas whose ring key is `any` (they will be *specialised* to `mode`'s ring);
   3. lemmas at a different ring or unitality, which will need a conversion in step 5 —
      ordered by the length of the conversion path.

   Within a group, higher attribute priority first, then fewer holes first (a lemma with no
   holes, like `cfc_pow_id`, is more specific than `cfc_pow` and produces fewer side goals).

   Applying a candidate:
   1. Instantiate the lemma with metavariables.
   2. Assign the lemma's `A`, `R`, `p` and *element* arguments from the target mode. Assigning
      the element **before** matching is what makes lemmas whose algebra side does not mention
      the element (like `cfc_const_one : cfc (fun _ ↦ 1) a = 1`) work, and what forces lemmas
      like `cfc_pow_id` to match only at the right element.
   3. Synthesise all instance-implicit arguments. Failure here rejects the candidate — this is
      how `cfc_sub` is prevented from being used over `ℝ≥0`, and how `RCLike` lemmas are
      restricted to `RCLike` rings.
   4. Replace the holes of the algebra side by fresh metavariables and unify the result with `e`
      at reducible transparency.
   5. Recurse on the terms the holes were matched against, at the *lemma's* mode.
   6. Assign the recursively found functions to the lemma's function variables, discharge or
      collect the remaining hypotheses (§7), and assemble the proof:
      `e = ⟨algebra side⟩` by congruence, then the lemma itself, then β-reduce the resulting
      function.

4. **Tagged pull lemmas at a different element.** If nothing above worked, try the *hole-free*
   candidates again without fixing the element: `e` is rewritten to `cfc F b` for whatever
   element `b` the lemma matches, and the algorithm re-enters at step 2, which turns the
   mismatch into a composition. This is what makes `NormedSpace.exp (I • a)` work: it becomes
   `cfc Complex.exp (I • a)` and then, via `cfc_comp_smul`, `cfc (fun x ↦ Complex.exp (I * x)) a`.

   Only hole-free lemmas are eligible, since the holes of a lemma applied at an unknown element
   would themselves be applications of the calculus at that unknown element.

5. **Failure.** If no candidate applies, `pull` fails for `e`. The trace records every candidate
   considered and why it was rejected.

6. **Conversion.** Steps 1–4 may produce a result at a mode `m'` different from the requested
   `mode`. It is converted in two stages, unitality first, then the scalar ring:
   * `cfcₙ f a = cfc f a` (`Unital` category) — used left-to-right to make a non-unital result
     unital, right-to-left in the other direction. Doing this first keeps the `f 0 = 0` side
     goal about the smallest possible function, and implements the draft's rule that a `cfcₙ`
     at the right element should immediately become a `cfc` in `+unital` mode.
   * a shortest path in the `Scalar` graph from `m'`'s ring to `mode`'s ring.

   If no conversion exists, the result is rejected and the caller backtracks.

### 6.3 Termination

The recursion is structural in `e` except for step 2, where `Compose` lemmas replace `b` by a
subterm, step 4, which replaces `e` by a `cfc` application at a subterm of `e`, and step 6, which
is not recursive. A `maxDepth` guard (default 48) is nevertheless enforced, so that a
badly-tagged lemma set degrades into an error rather than a hang.

## 7. Side goals

Every hypothesis of an applied lemma that is not an instance and not discharged becomes a side
goal. The tactic handles them as follows.

* Hypotheses defeq to `p a` for the mode of the lemma are assigned the cached, shared `?ha`
  metavariable (§4).
* Everything else — `ContinuousOn f (spectrum R a)`, `ContinuousOn f (σₙ R a)`, `f 0 = 0`,
  `∀ x ∈ spectrum R a, f x ≠ 0`, … — becomes a fresh synthetic-opaque metavariable, `autoParam`
  wrappers stripped so the goal displays cleanly, and **named after its kind**:
  `cfc_pull.predicate`, `cfc_pull.continuity`, `cfc_pull.mapZero` or `cfc_pull.side`. The name
  lets the user address a whole group at once with `case cfc_pull.continuity => fun_prop`.
* Once the whole pull is finished (so that no function metavariables remain), the frontend
  deduplicates the goals and tries, on each: `assumption`, then the auto-param tactic the
  calculus API itself would use for a hypothesis of that kind (`cfc_cont_tac` for continuity,
  `cfc_zero_tac` for `f 0 = 0`, and for the rest `cfc_predicate`/`cfcₙ_predicate` followed by
  `cfc_tac` — in that order, because `cfc_tac` never fails).
* On a `cfc_pull.side` goal that survives all of that, the `(disch := tac)` tactic is tried
  last. These are the hypotheses peculiar to an individual lemma, the only ones the calculus API
  has nothing to offer for; the other three kinds already have a tactic written for them, and
  running a user tactic after it would mostly mean running `fun_prop` twice on the same
  `ContinuousOn` goal. The discharger is run as a separate attempt rather than as another branch
  of the `first` above, because that `first` ends in `cfc_tac`, which never fails.
* Anything still open is **an error**, listing the goals. With `+defer` they are returned and
  added to the goal list after the main goal instead.

Note that `+defer` does not switch the discharging off; it only changes what happens to the
survivors. The reason is that "discharge the easy ones and hand me the rest" is by far the most
useful behaviour, and it is what the messy examples in `MathlibTest/CFCPull/Examples.lean` rely
on. If you want to see the raw side goals, `set_option trace.Tactic.cfc_pull true` reports each
one as it is created and what became of it.

## 8. Worked examples

### 8.1 A simple pull

```lean
example (ha : p a) : star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a
```

Setup: `A` is the type of `a`; `ContinuousFunctionalCalculus R A ?p` synthesises and assigns
`?p := p`; the shared `?ha : p a` is created and later closed by `assumption`.

The goal is `Eq`, so both sides are pulled.

*Right-hand side.* Step 2 matches `cfc (fun x : R ↦ star x * x) a` with `b := a`, mode already
correct; the result is the function itself with proof `rfl`.

*Left-hand side.* Step 1 fails (`star a * a` is not `a`). Step 3 looks up `HMul.hMul` and finds
`cfc_mul`, ring key `any`, unital. Its algebra side `cfc ?f ?a * cfc ?g ?a` has two holes;
after replacing them the pattern is `?x₁ * ?x₂`, which unifies with `star a * a`.

* Recursing on `star a`: step 3 finds `cfc_star`, whose algebra side is `star (cfc ?f ?a)`, one
  hole; the pattern `star ?x` matches, and recursing on `a` hits step 1, giving `fun x ↦ x`.
  So `star a = cfc (fun x ↦ star ((fun y ↦ y) x)) a`, β-reduced to `fun x ↦ star x`.
* Recursing on `a`: step 1, `fun x ↦ x`.

`cfc_mul` then gives `star a * a = cfc (fun x ↦ star x * x) a`, with side goals
`ContinuousOn (fun x ↦ star x) (spectrum R a)` and `ContinuousOn (fun x ↦ x) (spectrum R a)`,
plus the shared `p a`.

Both sides now read `cfc (fun x ↦ star x * x) a`, so the main goal is closed by `rfl` and only
the side goals remain, and all of them are discharged automatically.

### 8.2 Changing scalar ring and unitality

```lean
example (ha : IsSelfAdjoint a) : a⁺ = cfc (fun z : ℂ ↦ (z.re⁺ : ℝ)) a := by
  cfc_pull ℂ a
```

Setup determines mode `(ℂ, unital)` with predicate `IsStarNormal`.

The left-hand side `a⁺` has head `posPart`. The index yields `CFC.posPart_def`, whose mode is
`(ℝ, non-unital)` — neither the ring nor the unitality matches, but a conversion path exists, so
it is tried (step 3, group 3). It has no holes, so it applies immediately, giving
`a⁺ = cfcₙ (·⁺ : ℝ → ℝ) a` at mode `(ℝ, non-unital)`.

Step 5 then converts: first `cfcₙ_eq_cfc` (side goals `ContinuousOn (·⁺) (σₙ ℝ a)` and
`(0 : ℝ)⁺ = 0`, and the shared `IsSelfAdjoint a`), then the single `Scalar` edge
`cfc_real_eq_complex` (side goal: the same shared `IsSelfAdjoint a`), producing
`a⁺ = cfc (fun z : ℂ ↦ ((z.re)⁺ : ℝ)) a`.

Both sides agree and `rfl` closes the goal.

### 8.3 Composition

```lean
example (ha : p a) (hf : ContinuousOn f ((· ^ 2) '' spectrum R a)) :
    cfc f (a ^ 2) = cfc (fun x ↦ f (x ^ 2)) a := by
  cfc_pull R a
```

The left-hand side is `cfc f (a ^ 2)`; step 2 applies, `a ^ 2` is not defeq to `a`, so its head
`HPow.hPow` is looked up in the `Compose` index, finding `cfc_comp_pow`. Its structured element
`?a ^ ?n` unifies with `a ^ 2` giving `?a := a`, which *is* our element, so the recursion stops
immediately with `cfc (fun x ↦ f (x ^ 2)) a`.

Had `?a` been something else — as in `cfc f ((cfc g a) ^ 2)` — the algorithm would simply
recurse on `cfc (fun x ↦ f (x ^ 2)) (cfc g a)`, re-entering step 2, matching `cfc g a` against
`a` this time, and closing with `cfc_comp'`.

### 8.4 From the wild

```lean
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a
```

Mode `(ℂ, unital)`. On the left:

* `HAdd.hAdd` ⇝ `cfc_add` (ring key `any`), two holes.
* `a` ⇝ step 1 ⇝ `fun x : ℂ ↦ x`.
* `I • cfcₙ √(1 - a ^ 2)` ⇝ `cfc_const_mul` is preferred over `cfc_smul` because its scalar
  argument lives in the target ring `ℂ`; one hole, matched against `cfcₙ √(1 - a ^ 2)`.
* `cfcₙ Real.sqrt (1 - a ^ 2)` ⇝ step 2 at mode `(ℝ, non-unital)`; `1 - a ^ 2` is not `a` and
  has no `Compose` lemma for `HSub.hSub`, so recurse on `1 - a ^ 2` at `(ℝ, non-unital)`:
  `cfcₙ_sub`, `cfcₙ_const_one`(*), `cfcₙ_pow` ⇝ `fun x : ℝ ↦ 1 - x ^ 2`. Then `cfcₙ_comp'`
  gives `cfcₙ (fun x : ℝ ↦ √(1 - x ^ 2)) a`, and step 5 converts to `(ℂ, unital)`.

  (*) in a *unital* algebra `1 - a ^ 2` is naturally handled by the unital lemmas; in that case
  the sub-pull is done at `(ℝ, unital)` and step 5 has only the scalar conversion to do.

The result is `cfc (fun x : ℂ ↦ x + I * ↑√(1 - x.re ^ 2)) a`. Note this is *not* syntactically
the right-hand side (`↑x.re` versus `x`); both are correct, and `rfl` fails. This is expected
and is exactly the situation `cfc_pull` is designed for: the user finishes with `cfc_congr`.

## 9. Lemmas to tag

This is the set tagged in `Mathlib/Tactic/CFCPull/Lemmas.lean`; `#cfc_pull_lemmas` prints it.
"Generic" means ring key `any`.

**`Id`**: `cfc_id'`, `cfcₙ_id'`.

**`Pull`, generic, unital**: `cfc_add`, `cfc_sub`, `cfc_neg`, `cfc_mul`, `cfc_pow`, `cfc_smul`,
`cfc_star`, `cfc_const`, `cfc_const_one`, `cfc_const_zero`, `cfc_const_add`, `cfc_add_const`,
`cfc_inv`, `cfc_inv_id`, `cfc_zpow`, `cfc_ringInverse_id`, `cfc_map_div`; the hole-free
specialisations `cfc_neg_id`, `cfc_pow_id`, `cfc_smul_id`, `cfc_star_id`; and, at priority 1100,
`cfc_const_mul` and `cfc_const_mul_id` (preferred over `cfc_smul` so that a scalar already living
in the target ring produces `r * f x` rather than `r • f x`).

**`Pull`, generic, non-unital**: `cfcₙ_add`, `cfcₙ_sub`, `cfcₙ_neg`, `cfcₙ_mul`, `cfcₙ_smul`,
`cfcₙ_star`, `cfcₙ_const_zero`, `cfcₙ_neg_id`, `cfcₙ_smul_id`, `cfcₙ_star_id`, and at priority
1100 `cfcₙ_const_mul`, `cfcₙ_const_mul_id`.

**`Pull`, concrete ring**: `CFC.posPart_def`, `CFC.negPart_def` (`ℝ`, non-unital);
`CFC.sqrt_def` (`ℝ≥0`, non-unital), `CFC.sqrt_eq_cfc` (`ℝ≥0`, unital),
`CFC.sqrt_eq_real_sqrt` (`ℝ`, non-unital), `CFC.abs_def` (`ℝ≥0`, non-unital, at the element
`star a * a`); `CFC.nnrpow_def` (`ℝ≥0`, non-unital), `CFC.rpow_def` (`ℝ≥0`, unital),
`CFC.rpow_eq_cfc_real` (`ℝ`, unital); `CFC.log_def` (`ℝ`, unital);
`CFC.exp_eq_normedSpace_exp` (generic — it is stated for `RCLike 𝕜`) with
`CFC.real_exp_eq_normedSpace_exp` and `CFC.complex_exp_eq_normedSpace_exp` at priority 1100 so
that `Real.exp`/`Complex.exp` are produced in preference to `NormedSpace.exp`.

Note that when several lemmas describe the same operation at different rings, the candidate
ordering picks the right one on its own: at target ring `ℝ`, `CFC.sqrt_eq_real_sqrt` costs
nothing while `CFC.sqrt_def` costs a scalar conversion, and at `ℝ≥0` the `ℝ` lemma is discarded
because there is no conversion `ℝ → ℝ≥0`.

`CFC.sqrt_def`, `CFC.abs_def` and `CFC.log_def` did not exist in Mathlib and are added (all are
`rfl`) alongside the tags.

**`Scalar`**: `cfc_nnreal_eq_real`, `cfcₙ_nnreal_eq_real`, `cfc_real_eq_complex`,
`cfcₙ_real_eq_complex`. The reverse directions (`cfc_real_eq_nnreal`, `cfc_complex_eq_real`)
carry non-syntactic hypotheses and are deliberately *not* tagged.

**`Unital`**: `cfcₙ_eq_cfc`.

**`Compose`**: `cfc_comp'`, `cfcₙ_comp'` (head symbol `cfc`/`cfcₙ`; the fallbacks used by step 2),
`cfc_comp_pow`, `cfc_comp_smul`, `cfc_comp_star`, `cfc_comp_neg`, `cfc_comp_inv`,
`cfc_comp_zpow`, `cfc_comp_const_mul` (priority 1100), and the non-unital `cfcₙ_comp_smul`,
`cfcₙ_comp_star`, `cfcₙ_comp_neg`, `cfcₙ_comp_const_mul` (priority 1100).

`cfc_sum` and `cfcₙ_sum` are tagged, with their bound-hole warning silenced by
`set_option cfcPull.warnBoundHoles false`: they cannot pull *through* a sum, but they collect one
whose summands are already applications of the calculus, which is the second half of the staged
idiom in §11.

Not tagged: `cfc_apply_pi`, the polynomial lemmas (`cfc_map_polynomial`, `cfc_comp_polynomial`),
and the `Unitization` bridges.

## 10. Errors, tracing and limits

The tactic fails with a descriptive error when

* neither `R` nor `a` was given and none could be inferred from the goal;
* no continuous functional calculus instance exists for the requested mode;
* the goal has no argument of type `A` to pull on;
* `pull` fails on every candidate argument, in which case the error names the first expression
  it got stuck on and its head symbol.

`set_option trace.Tactic.cfc_pull true` reports, in a nested tree: the mode chosen and the
predicate found; for each subexpression, the candidate lemmas retrieved from the index, which
were rejected and why (ring mismatch, instance synthesis failure, pattern mismatch, recursive
failure); which hypotheses were filled from the cache and which became side goals; and the
conversions applied.

## 11. Deliberate non-goals and future work

* **Choosing the best scalar ring automatically.** The tactic converts each subterm to the
  requested ring as soon as it is produced, which can convert twice where once would do (e.g.
  `a⁺ - a⁻` at `ℂ` converts each summand rather than the difference). A later iteration could
  run an inference pass first to pick, for each node, the largest ring that works.
* **Side-goal ergonomics.** Grouping `ContinuousOn` goals into a single conjunction. (Naming the
  groups is done: see §7.)
* **Building `ContinuousOn` proofs during the traversal** rather than deferring them.
* **Recursing under a binder** (`cfc_sum`, `cfc_apply_pi`) — for which there is a good workaround,
  so this may never need doing.

  **The workaround.** `conv` can go under the binder, and once there the bound variable is an
  ordinary local hypothesis and `cfc_pull` is an ordinary pull:

  ```lean
  example (ha : p a) (hg : ∀ i, ContinuousOn (g i) (spectrum R a)) :
      ∑ i ∈ s, star (cfc (g i) a) = cfc (∑ i ∈ s, fun x ↦ star (g i x)) a := by
    conv_lhs => enter [2, i]; cfc_pull R a
    cfc_pull +defer R a
  ```

  The first line pulls each summand to `cfc (fun x ↦ star (g i x)) a`; the second lets `cfc_sum`
  collect them. (`enter [2, i]`, not `ext i`: `conv` must enter `Finset.sum`'s function argument
  before it can go under the lambda.) This leaves the side goal
  `∀ i ∈ s, ContinuousOn (fun x ↦ star (g i x)) (spectrum R a)`.

  **What a built-in version would take.** Two things, not the three claimed in an earlier draft
  of this document:

  1. *Matching.* The placeholder would have to be function-valued, `?b : ι → A`, so that the
     pattern reads `∑ i ∈ s, ?b i`. That part is easy — it is a Miller pattern and Lean's
     unifier solves it — but it needs its own code path, since `abstractHoles` currently
     substitutes an element-valued metavariable.
  2. *Recursion.* `pull` would have to run under `withLocalDecl i : ι` and return a family
     `f : ι → R → R` with a pointwise proof, rather than a single function and a single
     equation. Side goals raised under the binder would have to be generalised over `i` before
     being handed back, and `Result` would have to carry the binder. This touches every
     signature in `Core.lean`, and is the whole cost.

  Congruence, contrary to that earlier draft, is *not* an obstacle and needs no `@[congr]`
  machinery: with a function-valued hole, `funext` on the pointwise proofs followed by
  `mkCongrArg (Finset.sum s)` gives the step, uniformly for any binder-introducing head symbol.

  What `@[congr]` lemmas *would* buy is better side goals. `funext` demands the pointwise
  equation for **all** `i`, so the side goals raised inside the binder generalise to `∀ i, …`,
  whereas `Finset.sum_congr` carries `i ∈ s` and would give `∀ i ∈ s, …`. That is precisely the
  form the `conv` workaround already produces, which is a further reason not to hurry.

* **Relations other than binary ones**, and `cfc_pull ... at h`.
* **Lemma placement.** The `@[cfc_pull]` tags should move from
  `Mathlib/Tactic/CFCPull/Lemmas.lean` to the declaration sites, along with the three `rfl`
  lemmas that file adds.
* **Side goals in `conv` mode.** `conv` cannot carry unsolved goals out of a block, so anything
  the auto-param tactics fail to close is an error there, and `+defer` cannot help. Some `conv`
  tactics (`equals`) let the user prove the obligation inline; whether something similar makes
  sense for `cfc_pull` has not been investigated.
