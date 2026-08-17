/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Tactic.CFCPull
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Failure modes of `cfc_pull`

Every way `cfc_pull` and its attribute can fail, pinned down with `#guard_msgs`. This is partly
regression testing and partly documentation: these messages are what a user sees when something
goes wrong, so it is worth keeping them legible.
-/

@[expose] public section

open scoped NNReal

section Tactic

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a b : A}

/-! ### Failures in the tactic -/

/- Nothing in the goal has the type of the element. -/
/--
error: `cfc_pull` found nothing of type `A` in the goal
  2 = 2
-/
#guard_msgs in
example (ha : IsStarNormal a) : (2 : ℕ) = 2 := by
  cfc_pull ℂ a

/- Neither the scalar ring nor the element was given, and the goal mentions no calculus to read
them off. -/
/--
error: `cfc_pull` could not find an application of `cfc` or `cfcₙ` in the goal from which to read off the scalar ring and the element; supply them explicitly, as in `cfc_pull ℝ a`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull

/- The first positional argument is the ring, so giving the element alone does not work. -/
/--
error: `cfc_pull`'s first argument is the scalar ring, but `a` did not elaborate as a type:
  type expected, got
    (a : A)
If `a` is the element to pull towards, give the scalar ring as well, as in `cfc_pull ℝ a`.
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_pull a

/- There is no functional calculus over the requested ring. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` could not even state `NonUnitalContinuousFunctionalCalculus ℚ A _`; the algebra is missing some of the structure the continuous functional calculus needs
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull ℚ a

/- No tagged lemma applies to the head symbol; here there is not even a head constant. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `f a`
    (head symbol: _, target: cfc over ℂ)
-/
#guard_msgs in
example (ha : IsStarNormal a) (f : A → A) : f a = f a := by
  cfc_pull ℂ a

/- The expression is built from an element other than the one being pulled towards. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `star b * b`
    (head symbol: HMul.hMul, target: cfc over ℂ)
-/
#guard_msgs in
example (ha : IsStarNormal a) : star b * b = star b * b := by
  cfc_pull ℂ a

/- The depth guard fires. Note that it aborts the whole run rather than being treated as one
more failed candidate, so the reason reported is the real one. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` reached its maximum recursion depth of 1; either the expression is more deeply nested than that, or the `@[cfc_pull]` lemma set is looping. Raise the limit with `cfc_pull (maxDepth := 2) ..`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull (maxDepth := 1) ℂ a

/- `CFC.posPart_def` lives over `ℝ`, and there is no tagged conversion `ℝ → ℝ≥0` (there cannot be
a syntactic one: it would need the function to be nonnegative on the spectrum). So the lemma is
not even offered as a candidate and the pull gets stuck;
`set_option trace.Tactic.cfc_pull true` reports the lemmas skipped for this reason. -/
/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `a⁺`
    (head symbol: PosPart.posPart, target: cfc over ℝ≥0)
-/
#guard_msgs in
example (ha : IsSelfAdjoint a) : a⁺ = a⁺ := by
  cfc_pull ℝ≥0 a

/- A `conv` block cannot end with unsolved goals, so in `conv` mode a surviving side goal is an
error. This is not specific to `cfc_pull`: `conv => rw [h]` with a side condition fails the same
way. Use `+discharge`, or put the hypotheses in context. -/
/--
error: Tactic `conv` failed: There are unsolved goals
case cfc_pull
A : Type u_1
inst✝² : CStarAlgebra A
inst✝¹ : PartialOrder A
inst✝ : StarOrderedRing A
a b : A
ha : IsStarNormal a
f g : ℂ → ℂ
⊢ ContinuousOn f (spectrum ℂ a)

case cfc_pull
A : Type u_1
inst✝² : CStarAlgebra A
inst✝¹ : PartialOrder A
inst✝ : StarOrderedRing A
a b : A
ha : IsStarNormal a
f g : ℂ → ℂ
⊢ ContinuousOn g (spectrum ℂ a)
-/
#guard_msgs in
example (ha : IsStarNormal a) (f g : ℂ → ℂ) :
    cfc f a * cfc g a + b = cfc (fun x ↦ f x * g x) a + b := by
  conv_lhs => arg 1; cfc_pull ℂ a

end Tactic

section Attribute

/-! ### Failures of the `@[cfc_pull]` attribute -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- Not an equation at all. -/
theorem cfcPullTest.notAnEquation : True := trivial

/-- error: `cfcPullTest.notAnEquation` is not an equation -/
#guard_msgs in
attribute [cfc_pull] cfcPullTest.notAnEquation

/-- An equation, but neither side is an application of the calculus. -/
omit [Ring A] [StarRing A] [TopologicalSpace A] in
theorem cfcPullTest.noCFC (a : A) : a = a := rfl

/--
error: @[cfc_pull] failed: neither side of `cfcPullTest.noCFC` has `cfc` or `cfcₙ` as its head symbol.
  ?a = ?a
-/
#guard_msgs in
attribute [cfc_pull] cfcPullTest.noCFC

/-- Both sides are the same calculus at the same element. -/
theorem cfcPullTest.sameSides (f : R → R) (a : A) : cfc f a = cfc f a := rfl

/--
error: @[cfc_pull] failed: both sides of `cfcPullTest.sameSides` are applications of the same functional calculus to the same element; there is nothing for `cfc_pull` to do.
-/
#guard_msgs in
attribute [cfc_pull] cfcPullTest.sameSides

/-- Both sides apply the calculus to elements of the same size, so there is no way to tell which
direction the lemma is meant to be used in. -/
theorem cfcPullTest.equalSizes (f : R → R) (a b : A) (h : a = b) : cfc f a = cfc f b := by rw [h]

/--
error: @[cfc_pull] failed: `cfcPullTest.equalSizes` looks like a composition lemma, but neither side applies the functional calculus to a more complicated element than the other.
-/
#guard_msgs in
attribute [cfc_pull] cfcPullTest.equalSizes

/-- The non-`cfc` side is a bare variable other than the element, so there is nothing to index the
lemma under. -/
theorem cfcPullTest.noHead (f : R → R) (a b : A) (h : cfc f a = b) : cfc f a = b := h

/--
error: @[cfc_pull] failed: the non-`cfc` side of `cfcPullTest.noHead` is `?b`, which has no head symbol to index on.
-/
#guard_msgs in
attribute [cfc_pull] cfcPullTest.noHead

end Attribute

section BothChange

/-- Changing the scalar ring and the unitality at once is not supported, even though the
statement is perfectly true. Split it into `cfcₙ_eq_cfc` and `cfc_real_eq_complex`, both of which
are tagged. -/
theorem cfcPullTest.ringAndUnitality {A : Type*} [CStarAlgebra A] {a : A} (f : ℝ → ℝ)
    (hf : ContinuousOn f (quasispectrum ℝ a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfc (fun x : ℂ ↦ (f x.re : ℂ)) a := by
  rw [cfcₙ_eq_cfc, cfc_real_eq_complex]

/--
error: @[cfc_pull] failed: `cfcPullTest.ringAndUnitality` changes both the scalar ring and the unitality of the functional calculus; such lemmas are not supported.
-/
#guard_msgs in
attribute [cfc_pull] cfcPullTest.ringAndUnitality

end BothChange

section BoundHoles

/- `cfc_sum` applies the calculus underneath the `∑` binder. Tagging it is legitimate — it *is*
tagged in `Mathlib/Tactic/CFCPull/Lemmas.lean` — but by default the attribute points out that
the position will not be recursed into. -/
/--
warning: `cfc_sum` applies the functional calculus at `cfc (?f #0)
  ?a`, which mentions a bound variable. `cfc_pull` cannot recurse under a binder, so it will treat that position as part of the pattern rather than as a hole: the lemma will only apply when the position is already an application of the calculus.
-/
#guard_msgs in
attribute [cfc_pull] cfc_sum

/- `set_option cfcPull.warnBoundHoles false` is how a deliberate tag acknowledges this. -/
#guard_msgs in
set_option cfcPull.warnBoundHoles false in
attribute [cfc_pull] cfc_sum

end BoundHoles
