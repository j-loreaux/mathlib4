module

public import Mathlib

section GenericUnital

/- In these examples, the user would supply to the `cfc_pull` tactic that they want a
to use the unital `cfc`, the scalar ring `R`, and the element `a`.  -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
  [ContinuousMap.UniqueHom R A] {a : A} {f g : R → R}

example (ha : p a) :
    star a * a = cfc (fun x : R ↦ star x * x) a := by
  rw [cfc_mul .., cfc_star, cfc_id' ..]

example (ha : p a) (hf : ContinuousOn f (spectrum R a)) (hg : ContinuousOn g (spectrum R a)) :
    star (cfc f a) + cfc g a + a = cfc (fun x ↦ star (f x) + g x + x) a := by
  rw [cfc_add .., cfc_add .., cfc_star, cfc_id' ..]

example (ha : p a) :
    a ^ 2 + 3 • a * cfc (id : R → R) a = cfc (fun x : R ↦ x ^ 2 + 3 • x * x) a := by
  rw [cfc_id .., cfc_add .., cfc_pow_id .., cfc_mul .., cfc_smul_id .., cfc_id' ..]

example (ha : p a) (hf : ContinuousOn f ((· ^ 2) '' spectrum R a)) :
    cfc f (a ^ 2) = cfc (fun x ↦ f (x ^ 2)) a := by
  rw [cfc_comp_pow ..]

example (ha : p a) (hf : Continuous f) (hg : ContinuousOn g (spectrum R a)) :
    cfc f ((cfc g a) ^ 2) = cfc (fun x ↦ f (g x ^ 2)) a := by
  rw [← cfc_comp_pow f 2 (cfc g a) (ha := cfc_predicate g a), cfc_comp' (fun x : R ↦ f (x ^ 2)) g a]

end GenericUnital

section GenericNonUnital

/- In these examples, the user would supply to the `cfc_pull` tactic that they want a
to use the non-unital `cfcₙ`, the scalar ring `R`, and the element `a`.  -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
  [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A]
  {a : A} {f g : R → R}

example (ha : p a) :
    star a * a = cfcₙ (fun x : R ↦ star x * x) a := by
  rw [cfcₙ_mul .., cfcₙ_star, cfcₙ_id' ..]

example (ha : p a) (hf : ContinuousOn f (quasispectrum R a)) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum R a)) (hg0 : g 0 = 0) :
    star (cfcₙ f a) + cfcₙ g a + a = cfcₙ (fun x ↦ star (f x) + g x + x) a := by
  rw [cfcₙ_add .., cfcₙ_add .., cfcₙ_star, cfcₙ_id' ..]

example (ha : p a) :
    a * a + 3 • a * cfcₙ (id : R → R) a = cfcₙ (fun x : R ↦ x * x + 3 • x * x) a := by
  rw [cfcₙ_id .., cfcₙ_add .., cfcₙ_mul .., cfcₙ_id' ..,
    cfcₙ_mul .., cfcₙ_smul_id .., cfcₙ_id' ..]

example (ha : p a) (hf : ContinuousOn f ((· ^ 2) '' quasispectrum R a)) (hf0 : f 0 = 0) :
    cfcₙ f (a * a) = cfcₙ (fun x ↦ f (x ^ 2)) a := by
  simp only [pow_two] at hf ⊢
  rw [cfcₙ_comp' f (fun x : R ↦ x * x) a, cfcₙ_mul .., cfcₙ_id' ..]

example (ha : p a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum R a)) (hg0 : g 0 = 0) :
    cfcₙ f (cfcₙ g a * cfcₙ g a) = cfcₙ (fun x ↦ f (g x * g x)) a := by
  have h2 := cfcₙ_comp' f (fun y : R ↦ y * y) (cfcₙ g a) (ha := cfcₙ_predicate g a)
  have h3 : cfcₙ (fun x : R ↦ f (g x * g x)) a = cfcₙ (fun y : R ↦ f (y * y)) (cfcₙ g a) :=
    cfcₙ_comp' (fun y : R ↦ f (y * y)) g a
  have h1 : cfcₙ (fun y : R ↦ y * y) (cfcₙ g a) = cfcₙ g a * cfcₙ g a :=
    cfcₙ_mul .. |>.trans (by rw [cfcₙ_id' R (cfcₙ g a) (cfcₙ_predicate g a)])
  rw [h3, h2, h1]

end GenericNonUnital

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open Complex
open scoped NNReal

example (ha : IsStarNormal a) :
    NormedSpace.exp (I • a) = cfc (fun x ↦ exp (I • x)) a := by
  sorry

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp (I • a) = cfc (fun x ↦ exp (I • x)) a := by
  sorry

example (ha : 0 ≤ a) :
    CFC.sqrt a = cfcₙ NNReal.sqrt a := by
  sorry

-- In this example, the user specifies they want to work over the scalar ring `ℝ`
example (ha : 0 ≤ a) :
    1 - CFC.sqrt a = cfc (fun x ↦ 1 - √x) a := by
  sorry

/- In this example, a side goal should be generated for the continuity of `f` on
the appropriate set, so `cfc_pull` won't close the goal entirely by itself.
The user specifies that they want a `cfc` to act on the element `CFC.sqrt (a ^ 2)`. -/
example (ha : IsSelfAdjoint a) (f : ℝ≥0 → ℝ≥0) (hf0 : f 0 = 0) :
    CFC.sqrt (CFC.sqrt (a ^ 2)) + cfcₙ f (CFC.sqrt (a ^ 2)) =
      cfcₙ (fun x ↦ NNReal.sqrt x + f x) (CFC.sqrt (a ^ 2)) := by
  sorry

example (ha : IsSelfAdjoint a) :
    a⁺ = cfc (fun z : ℂ ↦ z.re⁺) a := by
  sorry

#exit

-- `a⁺`/`a⁻` (posPart/negPart), keeping the non-unital `cfcₙ` head even in a unital algebra
example (ha : IsSelfAdjoint a) :
    a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  sorry

example :
    a⁺ * a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ * x⁻) a := by
  sorry

-- mixing the (non-unital) `a⁺` with the unital constant `1`, forcing a `cfc` head
example (ha : IsSelfAdjoint a) :
    1 - a⁺ = cfc (fun x : ℝ ↦ 1 - x⁺) a := by
  sorry

-- `CFC.abs`, pulled over its own scalar ring `ℝ≥0` at the base point `star a * a`
example (a : A) :
    CFC.abs a * CFC.abs a = cfcₙ (fun x : ℝ≥0 ↦ NNReal.sqrt x * NNReal.sqrt x) (star a * a) := by
  sorry

-- `a ^ (x : ℝ)`, changing the scalar ring to `ℝ≥0` for the pulled function
example (a : A) (x : ℝ) :
    a ^ x = cfc (fun t : ℝ≥0 ↦ t ^ x) a := by
  sorry

example (ha : 0 ≤ a) (x y : ℝ) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  sorry

-- The non-unital `cfcₙ` used on an element of a unital `CStarAlgebra`, over `a ^ (y : ℝ≥0)`
example (ha : 0 ≤ a) (y z : ℝ≥0) :
    a ^ y * a ^ z = cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t y * NNReal.nnrpow t z) a := by
  sorry

example (ha : 0 ≤ a) :
    CFC.sqrt a * CFC.sqrt a = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.sqrt t) a := by
  sorry

-- `NormedSpace.exp`, changing the scalar ring between `ℂ` and `ℝ`
example (ha : IsSelfAdjoint a) :
    NormedSpace.exp a = cfc Real.exp a := by
  sorry

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp a * NormedSpace.exp a = cfc (fun x : ℝ ↦ Real.exp x * Real.exp x) a := by
  sorry

example (ha : IsStarNormal a) (z : ℂ) :
    NormedSpace.exp (z • a) = cfc (fun w : ℂ ↦ Complex.exp (z * w)) a := by
  sorry

-- `CFC.log` composed with `NormedSpace.exp`, pulled (not simplified away) into a single `cfc`
example (ha : IsSelfAdjoint a) :
    CFC.log (NormedSpace.exp a) = cfc (fun x : ℝ ↦ Real.log (Real.exp x)) a := by
  sorry

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp (-a) * NormedSpace.exp a = cfc (fun x : ℝ ↦ Real.exp (-x) * Real.exp x) a := by
  sorry

-- inversion in `Aˣ`, using the unital `cfc` even though `star a * a` alone would admit `cfcₙ`
example (a : Aˣ) (ha : IsStarNormal (a : A)) :
    (↑a⁻¹ : A) = cfc (fun x : ℂ ↦ x⁻¹) (a : A) := by
  sorry

example (ha : IsStarNormal a) (f g : ℂ → ℂ) (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    cfc f a * cfc g a = cfc (fun z ↦ f z * g z) a := by
  sorry

end CStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

open Complex
open scoped NNReal

example :
    a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  sorry

example :
    a⁺ * a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ * x⁻) a := by
  sorry

example (a : A) :
    CFC.abs a = cfcₙ NNReal.sqrt (star a * a) := by
  sorry

example (ha : 0 ≤ a) :
    CFC.sqrt a * CFC.sqrt a = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.sqrt t) a := by
  sorry

-- The user specifies that they want a `cfcₙ` to act on the element `star a * a`, not `a` itself
example (a : A) (f : ℝ≥0 → ℝ≥0) (hf0 : f 0 = 0) :
    CFC.sqrt (star a * a) + cfcₙ f (star a * a) =
      cfcₙ (fun x ↦ NNReal.sqrt x + f x) (star a * a) := by
  sorry

example (ha : IsStarNormal a) (f g : ℂ → ℂ) (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    cfcₙ f a * cfcₙ g a = cfcₙ (fun z ↦ f z * g z) a := by
  sorry

example (ha : IsSelfAdjoint a) :
    (-a)⁺ = cfcₙ (fun x : ℝ ↦ (-x)⁺) a := by
  sorry

-- relating `CFC.sqrt` to `nnrpow` (i.e. `a ^ (y : ℝ≥0)`), both pulled over `ℝ≥0`
example (ha : 0 ≤ a) (y : ℝ≥0) :
    CFC.sqrt a * a ^ y = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.nnrpow t y) a := by
  sorry

-- pulling `f` through `a⁺`, which is itself a `cfcₙ` application
example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf0 : f 0 = 0) :
    cfcₙ f a⁺ = cfcₙ (fun x ↦ f (x⁺)) a := by
  sorry

-- pulling `posPart` through a scalar multiple
example :
    (2 • a)⁺ = cfcₙ (fun x : ℝ ↦ (2 • x)⁺) a := by
  sorry

example (ha : 0 ≤ a) (y z : ℝ≥0) :
    a ^ y * a ^ z = cfcₙ (fun t : ℝ≥0 ↦ NNReal.nnrpow t y * NNReal.nnrpow t z) a := by
  sorry

-- changing the scalar ring to `ℂ`, mixing `star` with a scalar multiple
example (ha : IsStarNormal a) (z : ℂ) :
    z • star a = cfcₙ (fun w : ℂ ↦ z * star w) a := by
  sorry

end NonUnitalCStarAlgebra

section InTheWild

-- This section contains examples of goals that have appeared in Mathlib.

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open Complex
open scoped NNReal

-- hard: must convert from the `cfc` over `ℝ` to `ℂ`, and switch from non-unital to unital
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  sorry

/- very hard: same as the above, but starts from `CFC.sqrt (1 - a ^ 2)`.
this is especially hard because it's not obvious that `CFC.sqrt` should be
changed into `cfcₙ Real.sqrt (1 - a ^ 2)` and give the side goal `0 ≤ 1 - a ^ 2`
to the user. Arguably, `cfc_pull` should not succeed on this goal. -/
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  sorry

end InTheWild
