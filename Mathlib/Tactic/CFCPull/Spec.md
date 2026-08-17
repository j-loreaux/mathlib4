# Specification for the `cfc_pull` tactic

`cfc_pull` is a tactic used to automate the process of taking a term (generally in a C⋆-algebra,
but anything with a `ContinuousFunctionalCalculus` or `NonUnitalContinuousFunctionalCalculus`
instance will work) and proving (modulo some side goals collected and deferred for later) that
it is equal to another term with `cfc` (or `cfcₙ`) at the head of the expression.

This is useful for implementing a common technique for C⋆-algebras to show that two terms involving
the continuous functional calculus are equal. One first moves `cfc` to the head of the expression
within each term, and then applies `cfc_congr` to reduce the problem to showing that the
corresponding functions are equal on the spectrum.

## Simple examples

Consider the examples in `Examples.lean`. For each example, there is a term on the left-hand
side, and an equal term on the left-hand side with `cfc` (or `cfcₙ`) at the head of the expression.
Each of these examples should be solved by the `cfc_pull` tactic (modulo adding necessary
assumptions, or deferring them as side goals to be solved by the user, about continuity or whether
the element in question satisfies the relevant predicate involving that continuous functional
calculus).

## The `cfc_pull` attribute

This should become a Lean attribute used to mark lemmas (e.g., `@[cfc_pull]`) that should be used
by the `cfc_pull` tactic. Such lemmas should have the form in `Examples.lean` (possibly with the
equality in the reversed direction), where one side of the expression has a head symbol of `cfc`
(or `cfcₙ`) and the other side is a different head symbol (at reducible transparency). There will
be a handful of lemmas where both sides have `cfc` as the head symbol. This occurs, for example,
when switching between different scalar rings (as in [`cfc_nnreal_eq_real`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.html#cfc_real_eq_nnreal)) or switching between
the non-unital and unital functional calculi (as in [`cfcₙ_eq_cfc`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/NonUnital.html#cfc%E2%82%99_eq_cfc)), or for composition lemmas (as in [`cfc_comp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.html#cfc_comp) or [`cfc_comp_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.html#cfc_comp_pow)).

The processing for the `cfc_pull` attribute should categorize the lemma into one of
four possible categories:

1. Pull: these have `cfc` as the head symbol on only one side.
2. Scalar: these have `cfc` on both sides, but operate over different scalar rings
3. Unital: these lemmas relate `cfcₙ` to `cfc`.
4. Compose: these lemmas have `cfc` on both sides, but applied to different elements of the algebra.


For each category, different information should be stored by the attribute:

1. Pull lemmas should store: the head symbol (at reducible transparency, used for indexing) for
  the non-`cfc` side, the scalar ring used by the `cfc` and the function on which it's applied,
  and whether the `cfc` is unital or non-unital (i.e., `cfc` or `cfcₙ`).
2. Scalar lemmas should store: the scalar rings and whether it is unital or non-unital.
3. Unital lemmas should store the scalar ring.
4. Compose lemmas should store the scalar ring, unitality, and the head symbol inside the algebra
  element. For example, in `cfc_comp` the head symbol would *itself* be `cfc` (because the
  argument is `cfc f a`), whereas in `cfc_comp_pow` the head symbol would be `HPow.hPow` because
  the argument is `a ^ n`.

## Scalar rings

The scalar rings come in essentially 5 flavors: `ℂ`, `ℝ`, `ℝ≥0`, `𝕜` (with `RCLike 𝕜`), or
some generic commutative semiring `R`. Probably there should be an inductive type used by the
tactic representing each of these.

There is an ordering on these flavors which determines when a `cfc` expression over one either
applies generally or can be switched to one over the other flavor. This ordering is:
`ℝ≥0 → ℝ`, `ℝ → ℂ`, `𝕜 → ℝ`, `𝕜 → ℂ` and `R → _`.

(Note: now that I think about it, there should maybe be yet one more flavor: generic commutative
rings. In practice, the only concrete types we care about that fall into this category are `ℝ` and
`ℂ`, so it seems like `RCLike` suffices. However, some lemmas don't actually have that as a
hypothesis, e.g., `cfc_sub`, and only assume `CommRing`. I'm not sure whether this is a problem
or not, but let's table it for now, and only return to it if we determine it will cause issues.)

## Predicates

Attached to each scalar ring, there is a predciate associated the continuous functional calculus.
For `ℂ`, `ℝ` and `ℝ≥0`, there are `IsStarNormal`, `IsSelfAdjoint` and `(0 ≤ ·)`, respectively,
whereas for `𝕜` or `R`, it will be some variable `p : A → Prop` (this is an `outParam` determined
by the relevant `ContinuousFunctionalCalculus R A p` instance).

## Sketch of the behavior of the tactic by example

We'll analyze a few different examples highlighting the different kinds of
situations which may arise.

### Example 1: a simple pull example

Let's consider the first example from `Examples.lean`

```lean
variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
  [ContinuousMap.UniqueHom R A] {a : A} {f g : R → R}

example (ha : p a) :
    star a * a = cfc (fun x : R ↦ star x * x) a := by
  rw [cfc_mul .., cfc_star, cfc_id' ..]
```

The idea is that `cfc_mul`, `cfc_star` and `cfc_id'` would all be marked `@[cfc_pull]` and
categorized as pull lemmas. The user would supply information to the tactic, like the scalar
ring `R`, the element `a`, whether the cfc should be unital or not, and the expression
(given by a pattern e.g., `star _ * _`) in which to perform the pull. If no pattern is given,
then the expression is assumed to be an equality (or maybe and inequality?) and the pull operation
is performed on both sides. Specifying unitality should be optional (maybe with the `+unital`
syntax to specify the boolean value) because it can be determined from `a : A` by searching for
an instance of `One A` and defaulting to unital if instance search succeeds.

So, in this example, the user writes something like `cfc_pull R a` in place of the `rw`.
The tactic then proceeds as follows:

0. It gathers background information:
  + checks for the `One A` instance and determines that this is a unital problem.
  + categorizes the scalar ring `R` as a generic one, since it doesn't match `ℝ≥0`, `ℝ` or `ℂ`,
    and there is no `RCLike R` instance in context.
  + searches for a `ContinuousFunctionalCalculus R A ?p` instance, and assigns `?p` to `p`,
    so that now it knows the relevant predicate.
  + searches for and saves for future use `ha : p a`. It first checks the context and/or calls
    `cfc_tac` to produce this.
1. Sees that the head symbol is an equality, so proceeds to `cfc_pull` on both sides.
2. On the right, it sees `cfc` as the head symbol already *and, crucially* it is `cfc (_ : R → R) a`
  so it is already in the required form, so nothing is done.
3. On the left, it sees `HMul.hMul` as the head symbol.
4. It then looks up in its lemma index (registered with the `@[cfc_pull]` attribute) pull lemmas
  with the same head symbol (it's possible for there to be multiple lemmas; in such cases there
  should be additional information used to determine which one to pick, e.g., which scalar ring
  is being used) and satisfying the correct unitalit condition.
5. In this case, it would see that `cfcₙ_mul` and `cfc_mul` both have the correct head symbol,
  but only the latter is explicitly unital, so that one is preferred.
6. It then creates metavaribles `?f₁ : R → R` and `?g₁ : R → R`, `?hf₁ : cfc ?f₁ a = star a` and
  `?hg₁ : cfc ?g₁ a = a`. It creates additional metavariables for the `ContinuousOn` arguments of
  `cfc_mul`. It the creates the expression `star a * a = cfc (fun x ↦ ?f₁ x * ?g₁ x) a` using
  these metavariables and the lemma `cfc_mul`.
  At this point, once unification (later) assigns `?f₁` and `?g₁`, the tactic will have accomplished
  its goal.
7. It then recursively tries to perform `cfc_pull` on both `?hf₁` and `?hg₁`.
8. On `?hg₁` it sees `a`, since this is the variable we care about, it knows that it can use
  `cfc_id'` to get `cfc (fun x : R ↦ x) a = a`, and combining this with `?hg₁` it can produce
  a term of type `cfc ?g₁ a = cfc (fun x : R ↦ x) a`, which it then unifies to assign
  `?g₁ ≟ (fun x : R ↦ x)`.
9. On `?hf₁` it sees the head symbol `Star.star` and then searches the index to find `cfc_star`.
  It creates metavariables `?f₂ : R → R` and `?hf₂ : a = cfc ?f₂ a`. and it creates a term of
  type `cfc ?f₁ a = cfc (fun x ↦ star (?f₂ x)) a` using `?hf₁`, `?hf₂` and `cfc_star`, and then
  unification assigns `?f₁ ≟ fun x ↦ star (?f₂ x)`.
10. Finally, the recusion applies `cfc_pull` to `?hf₂`, similarly to step 8.
11. At this point all *function* metavariables created during this procedure
  have been assigned, which we consider success.
  Remaining metvariables are returned to the user. *Hopefully*(?) these should only
  be `ContinuousOn` goals, as the `p a` goals should be filled by the tactic in
  the process of creating the terms.
  In this particular case, the `ContinuousOn` goals should be solvable by
  `fun_prop`.

A few notes:

+ the procedure is deemed successful if all function metavariables are assigned.
+ errors can occur if no applicable indexed lemma matches the required
  specification, or if something during the initial background stage fails
+ the tactic should be written with `trace`ing available so that the user can
  inspect the failure by turning tracing on, and in particular to see which
  lemmas were (potentially) available, which matched, which hypotheses were
  automatically filled, etc.
+ while we could try to solve `ContinuousOn` goals in the process of the tactic
  using tools like `fun_prop`, let's try to avoid that for now as it adds an
  additional layer of complexity. Perhaps in a future iteration we can add this
  as an opt-in feature via a customization option.

### Example 2: changing scalar rings and unitality

Here's another example from `Examples.lean`

```lean
example (ha : IsSelfAdjoint a) :
    a⁺ = cfc (fun z : ℂ ↦ z.re⁺) a := by
  sorry
```

The idea here is that `CFC.posPart_def`, `cfc_real_eq_complex` and `cfcₙ_eq_cfc` are marked with
`@[cfc_pull]` and are categorized as pull, scalar and unital lemmas, respectively.

The example here works as follows, with the user requesting `cfc_pull +unital ℂ a`.
The tactic then proceeds as follows:

0. It gathers background information:
  + checks for the `One A` instance since the user requested `+unital`.
  + categorizes the scalar ring as `ℂ`
  + searches for a `ContinuousFunctionalCalculus ℂ A IsStarNormal` instance, since we already
    know what the predicate must be.
  + searches for and saves for future use `IsStarNormal a`. It first checks the context and doesn't
    find this, but `cfc_tac` should succeed in producing it.
1. sees an equality and that the right-hand side is already in the required form
2. on the left, sees the head symbol `PosPart.posPart` and looks up lemmas that match.
  In this case, it only finds `CFC.posPart_def`, which doesn't match the scalar ring (`ℝ` vs. `ℂ`)
  or unitality. However, this is okay because `ℝ → ℂ` in the scalar ring ordering and it's fine to
  use a non-unital lemma when you need a unital one (although unital specific lemmas should be
  preferred, when available).
4. So the tactic rewrites `a⁺` to `cfcₙ (fun x : ℝ → x⁺) a`. (side note: should there be a special
  class of `cfc_pull` lemmas called *unfold* lemmas?)
5. It then tries to recursively pull on this new expression. It sees `cfcₙ` as the head symbol,
  but it's got a `+unital` specification, so it's looking for `cfc`. It finds `cfcₙ_eq_cfc` and
  rewrites with that.
6. Finally, it has `cfc (fun x : ℝ → x⁺) a`, but it needs to work over the scalar ring `ℂ`, so it
  searches for a scalar ring transition lemma and finds `cfc_real_eq_complex`, but in order to do
  this, it needs an `IsSelfAdjoint a` hypothesis. It would be nice if the tactic could try to supply
  this automatically, but maybe that should be part of the background information step?

Some notes:

+ When in `+unital` mode, a match of the form `cfcₙ _ a` (where `a` is the element the user
  specified), should immediately opt for `cfcₙ_eq_cfc` even if the scalar ring doesn't match
  as this will minimize side goals moving forward.
+ I feel like changing the scalar ring should always happen last, if possible, but I'm not confident
  about this. I think there may be cases where this would be suboptimal.

### Example 3: composition

Care needs to be taken when the head symbol is `cfc` (or `cfcₙ`).
In the previous example, we addressed the case when we're working in the `+unital` setting on an
element `a`, over a scalar ring `R` and we match `cfc (_ : ?S → ?S) a` or `cfcₙ (_ : ?S → ?S) a`
where `?S` is a possibly different scalar ring from `R`. But there are times when we encounter
`cfc (_ : ?S → ?S) ?b` or `cfcₙ (_ : ?S → ?S) ?b` when the unification `?b ≟ a` fails (reducible transparency).
In these cases, what should be done?
Of course, in the `+unital` case, we should still switch `cfcₙ` to `cfc` with `cfcₙ_eq_cfc`.
When unification of `?S ≟ R` fails, then we should try to `cfc_pull` on `?b` with scalar ring `?S`,
*not* `R`.
Then, once we finish this, we switch the scalar ring to `R`.
Of course, if `?S` does not precede `R` in the ordering on scalar rings, we should stop and error.

Consider the following example from `Examples.lean`.

```lean
example (ha : p a) (hf : ContinuousOn f ((· ^ 2) '' spectrum R a)) :
    cfc f (a ^ 2) = cfc (fun x ↦ f (x ^ 2)) a := by
  rw [cfc_comp_pow ..]
```

So, in this example, the user writes something like `cfc_pull R a` in place of the `rw`.
The tactic then proceeds as follows:

0. It gathers background information:
  + checks for the `One A` instance and determines that this is a unital problem.
  + categorizes the scalar ring `R` as a generic one, since it doesn't match `ℝ≥0`, `ℝ` or `ℂ`,
    and there is no `RCLike R` instance in context.
  + searches for a `ContinuousFunctionalCalculus R A ?p` instance, and assigns `?p` to `p`,
    so that now it knows the relevant predicate.
  + searches for and saves for future use `ha : p a`. It first checks the context and/or calls
    `cfc_tac` to produce this.
1. Sees equality, and checks the right- and left-hand sides.
  The right-hand side already matches (`cfc (_ : R → R) a`).
2. The left-hand side matches `cfc (_ : R → R) ?b`, but `?b ≟ a` fails.
3. At this point, the tactic looks at the head symbol of `?b` (and finds `HPow.hPow`) and searches
  the index for a *compose* lemma whose head symbol (on the element of the algebra) matches.
  It finds `cfc_comp_pow`, so it creates a metavariable `?c : A` and assigns `?b = ?c ^ 2`.
  In this case, in fact this also assigns `?c = a`, and so `cfc_comp_pow` is an exact match and
  we're done. If it weren't the case that `?c = a`, then we would look at the head symbol of `?c`
  and search for yet another compose lemma. If the search fails, then we apply `cfc_pull`
  recursively to `?c`. if successful, we apply `cfc_comp` to the result.

### Example 4: an example from the wild

The following example from `Examples.lean` appears as a goal in Mathlib.

```lean
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  sorry
```

Here we `cfc_pull ℂ a` and the problem is determined to be unital. We sketch out how this should
be solved by the tactic with the ideas already in place:

0. gather background information
1. deal with equality and the right-hand side
2. match `HAdd.hAdd` and on the first argument use `cfc_id'`
3. on the second argument, use `cfc_const_mul` (preferred over `cfc_smul` because the scalar type
  `ℂ` matches the scalar ring we are going for.)
4. Try to pull (over `ℂ`) on `cfcₙ Real.sqrt (1 - a ^ 2)`. It's non-unital, so we switch to unital
  with `cfcₙ_eq_cfc`.
5. Try to pull (over `ℂ`) on `cfc Real.sqrt (1 - a ^ 2)`, but `1 - a ^ 2 ≟ a` fails, so we
  look for a compose lemma matching the head of `1 - a ^ 2` which is `HSub.hSub`; no such lemma
  is found.
6. Default to applying `cfc_comp` (over `ℝ`) with a metavariable of the form
  `?hf : 1 - a ^ 2 = cfc (?f : ℝ → ℝ) a`, and switching to the `ℂ` scalar ring via
  `cfc_real_eq_complex`
7. Try to pull (over `ℝ` now!) on `1 - a ^ 2`
  match on `HSub.hSub` and proceed as usual (as in the case of the simpler examples like Example 1).

## A non-exhaustive list of lemmas that should be tagged `cfc_pull`

Please fill this in.

## Other considerations

+ The heart of this tactic should live in `MetaM` and it should be fundamentally recursive.
+ The information gathering should probably live in `TacticM` since we'll likely need to access
  the local context.
+ It's possible this specification and / or the `Examples.lean` file are incomplete or that the
  examples don't *quite* match what the final tactic should produce.
+ It would be nice if there were some sort of convenient collecting / handling of side goals,
  but I'm not sure what is best. Ideas include:
  - grouping all `ContinuousOn` goals into a single conjunction, likewise with `?f 0 = 0` goals
  - providing user accessible names to goals which group them so that they may be solved with
    `case goal1 | goal2 | goal3 => by fun_prop`
  - trying to build terms for `ContinuousOn` goals using metavariables as you traverse the
    expression tree (I expect this to be hard).
  I recommend saving this kind of goal management for a future iteration of the tactic after we
  get the basic API up and running.
