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
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

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

/--
error: `cfc_pull` found nothing of type `A` in the goal
  2 = 2
-/
#guard_msgs in
example (ha : IsStarNormal a) : (2 : ℕ) = 2 := by
  cfc_pull ℂ a

/--
error: `cfc_pull` could not find an application of `cfc` or `cfcₙ` in the goal from
which to read off the scalar ring and the element; supply them explicitly, as in
`cfc_pull ℝ a`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull

/--
error: `cfc_pull`'s first argument is the scalar ring, but `a` did not elaborate as a type:
  type expected, got
    (a : A)
If `a` is the element to pull towards, give the scalar ring as well, as in `cfc_pull ℝ a`.
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = cfc (fun x : ℂ ↦ star x * x) a := by
  cfc_pull a

/--
error: `cfc_pull` made no progress
  `cfc_pull`: `A` has no non-unital continuous functional calculus over `ℚ`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull ℚ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `f a`
    (head symbol: _, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) (f : A → A) : f a = f a := by
  cfc_pull ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `star b * b`
    (head symbol: HMul.hMul, target: cfc over ℂ at `a`)
-/
#guard_msgs in
example (ha : IsStarNormal a) : star b * b = star b * b := by
  cfc_pull ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` reached its maximum recursion depth of 1; either
  the expression is more deeply nested than that, or the `@[cfc_pull]` lemma set is
  looping. Raise the limit with `cfc_pull (maxDepth := 2) ..`
-/
#guard_msgs in
example (ha : IsStarNormal a) : star a * a = star a * a := by
  cfc_pull (maxDepth := 1) ℂ a

/--
error: `cfc_pull` made no progress
  `cfc_pull` got stuck on `a⁺`
    (head symbol: PosPart.posPart, target: cfc over ℝ≥0 at `a`)
-/
#guard_msgs in
example (ha : IsSelfAdjoint a) : a⁺ = a⁺ := by
  cfc_pull ℝ≥0 a

/- Side goals that neither `assumption` nor the auto-param tactics can close are an error unless
`+defer` is given. -/
/--
error: `cfc_pull` rewrote the goal but could not discharge 2 side goals:
  case cfc_pull.continuity
  A : Type u_1
  inst✝² : CStarAlgebra A
  inst✝¹ : PartialOrder A
  inst✝ : StarOrderedRing A
  a b : A
  ha : IsStarNormal a
  f g : ℂ → ℂ
  ⊢ ContinuousOn f (spectrum ℂ a)

  case cfc_pull.continuity
  A : Type u_1
  inst✝² : CStarAlgebra A
  inst✝¹ : PartialOrder A
  inst✝ : StarOrderedRing A
  a b : A
  ha : IsStarNormal a
  f g : ℂ → ℂ
  ⊢ ContinuousOn g (spectrum ℂ a)
Use `cfc_pull +defer ..` to have them added to the goal list instead.
-/
#guard_msgs (whitespace := lax) in
example (ha : IsStarNormal a) (f g : ℂ → ℂ) :
    cfc f a * cfc g a = cfc (fun x ↦ f x * g x) a := by
  cfc_pull ℂ a

/- `+defer` does not help inside `conv`, which cannot end with unsolved goals — the same
restriction that `rw` inside `conv` is subject to. -/
/--
error: Tactic `conv` failed: There are unsolved goals
case cfc_pull.continuity
A : Type u_1
inst✝² : CStarAlgebra A
inst✝¹ : PartialOrder A
inst✝ : StarOrderedRing A
a b : A
ha : IsStarNormal a
f g : ℂ → ℂ
⊢ ContinuousOn f (spectrum ℂ a)

case cfc_pull.continuity
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
  conv_lhs => arg 1; cfc_pull +defer ℂ a

end Tactic

section Attribute

/-! ### Failures of the `@[cfc_pull]` attribute -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- error: `cfcPullTest.notAnEquation` is not an equation -/
#guard_msgs in
@[cfc_pull] theorem cfcPullTest.notAnEquation : True := trivial


omit [Ring A] [StarRing A] [TopologicalSpace A] in
/--
error: @[cfc_pull] failed: neither side of `cfcPullTest.noCFC` has `cfc` or `cfcₙ`
as its head symbol:
  ?a = ?a
-/
#guard_msgs in
@[cfc_pull] theorem cfcPullTest.noCFC (a : A) : a = a := rfl


/--
error: @[cfc_pull] failed: both sides of `cfcPullTest.sameSides` are applications of the same
functional calculus to the same element; there is nothing for `cfc_pull` to do.
-/
#guard_msgs in
@[cfc_pull]
theorem cfcPullTest.sameSides (f : R → R) (a : A) : cfc f a = cfc f a := rfl


/--
error: @[cfc_pull] failed: `cfcPullTest.equalSizes` looks like a composition lemma, but neither
side applies the functional calculus to a more complicated element than the other.
-/
#guard_msgs in
@[cfc_pull]
theorem cfcPullTest.equalSizes (f : R → R) (a b : A) (h : a = b) : cfc f a = cfc f b := by rw [h]


/--
error: @[cfc_pull] failed: the non-`cfc` side of `cfcPullTest.noHead` is `?b`,
which has no head symbol to index on.
-/
#guard_msgs in
@[cfc_pull] theorem cfcPullTest.noHead (f : R → R) (a b : A) (h : cfc f a = b) : cfc f a = b := h

end Attribute

section BothChange

/--
error: @[cfc_pull] failed: `cfcPullTest.ringAndUnitality` changes both the scalar ring and the
unitality of the functional calculus; such lemmas are not supported.
-/
#guard_msgs in
@[cfc_pull]
theorem cfcPullTest.ringAndUnitality {A : Type*} [CStarAlgebra A] {a : A} (f : ℝ → ℝ)
    (hf : ContinuousOn f (quasispectrum ℝ a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfc (fun x : ℂ ↦ (f x.re : ℂ)) a := by
  rw [cfcₙ_eq_cfc, cfc_real_eq_complex]

end BothChange

section BoundHoles

/--
warning: `cfc_sum` applies the functional calculus at
  cfc (?f #0) ?a
which mentions a bound variable. `cfc_pull` cannot recurse under a binder, so it will
treat that position as part of the pattern rather than as a hole: the lemma will only
apply when the position is already an application of the calculus.

If that is what you intend, silence this warning with
`set_option cfcPull.warnBoundHoles false in`.
-/
#guard_msgs in
attribute [cfc_pull] cfc_sum

end BoundHoles
