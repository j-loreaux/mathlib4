/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

import Mathlib.Algebra.Algebra.Spectrum.Pi

/-!
# Lemmas needed by the `cfc_pull` tactic

Some lemmas missing from Mathlib needed for the `cfc_pull` tactic.
-/

@[expose] public section

open scoped NNReal
open Topology ContinuousMap ContinuousMapZero

section Extend

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]

section Unital

variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- The `g := 0` case of `cfcHom_eq_cfc_extend`. -/
lemma cfcHom_eq_cfc_extend_zero {a : A} (ha : p a) (f : C(spectrum R a, R)) :
    cfcHom ha f = cfc (Function.extend Subtype.val f 0) a :=
  cfcHom_eq_cfc_extend 0 ha f

/-! ### Numerals

`cfc_const` covers `algebraMap R A r`; these cover the numerals, which are `Nat.cast` and
`Int.cast` into `A`. -/

lemma cfc_natCast (n : ℕ) (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ : R ↦ (n : R)) a = (n : A) := by
  rw [cfc_const _ a ha, map_natCast]

lemma cfc_ofNat (n : ℕ) [n.AtLeastTwo] (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ : R ↦ (OfNat.ofNat n : R)) a = (OfNat.ofNat n : A) :=
  cfc_natCast n a ha

end Unital

section IntCast

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
  [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

lemma cfc_intCast (n : ℤ) (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ : R ↦ (n : R)) a = (n : A) := by
  rw [cfc_const _ a ha, map_intCast]

end IntCast

section NonUnital

variable [Nontrivial R] [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [NonUnitalContinuousFunctionalCalculus R A p]

/-- The `g := 0` case of `cfcₙHom_eq_cfcₙ_extend`. -/
lemma cfcₙHom_eq_cfcₙ_extend_zero {a : A} (ha : p a) (f : C(quasispectrum R a, R)₀) :
    cfcₙHom ha f = cfcₙ (Function.extend Subtype.val f 0) a :=
  cfcₙHom_eq_cfcₙ_extend 0 ha f

end NonUnital

end Extend

section UnitalToNonUnital

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A]

/-- `cfc_pow` for `cfcₙ`, in a unital algebra: a non-unital ring has no powers, so there is no
general `cfcₙ_pow`. The exponent is a successor, since `cfcₙ f a ^ 0 = 1`. -/
lemma cfcₙ_pow_succ (f : R → R) (n : ℕ) (a : A)
    (hf : ContinuousOn f (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ f x ^ (n + 1)) a = cfcₙ f a ^ (n + 1) := by
  by_cases ha : p a
  · have hf' := hf.mono <| spectrum_subset_quasispectrum R a
    rw [cfcₙ_eq_cfc hf hf0, cfcₙ_eq_cfc (f := fun x ↦ f x ^ (n + 1)) (by fun_prop) (by simp [hf0]),
      cfc_pow f _ a hf' ha]
  · simp [cfcₙ_apply_of_not_predicate a ha]

end UnitalToNonUnital

/-! ### Homomorphisms and products at a fixed ring of scalars

`StarAlgHomClass.map_cfc`, `NonUnitalStarAlgHomClass.map_cfcₙ`, `cfc_map_prod` and
`cfcₙ_map_prod` have a ring of scalars `S` which occurs in neither side of the equation, and is
determined only by instances which are not `outParam`s, so `simp` cannot use them. These are their
specializations at `S := R` and at `S := ℂ`. -/

section MapCFC

variable {F R A B : Type*} {p : A → Prop} {q : B → Prop}
  [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A]
  [Ring B] [StarRing B] [TopologicalSpace B] [Algebra R B]
  [ContinuousFunctionalCalculus R A p] [ContinuousFunctionalCalculus R B q]
  [ContinuousMap.UniqueHom R B] [FunLike F A B] [StarHomClass F A B]

/-- `StarAlgHomClass.map_cfc` for an `R`-algebra homomorphism. -/
lemma StarAlgHomClass.map_cfc' [AlgHomClass F R A B] (φ : F) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hφ : Continuous φ := by fun_prop) (ha : p a := by cfc_tac) (hφa : q (φ a) := by cfc_tac) :
    φ (cfc f a) = cfc f (φ a) :=
  StarAlgHomClass.map_cfc (S := R) φ f a

/-- `StarAlgHomClass.map_cfc` for a `ℂ`-algebra homomorphism. -/
lemma StarAlgHomClass.map_cfc_complex [Algebra R ℂ] [Algebra ℂ A] [Algebra ℂ B]
    [IsScalarTower R ℂ A] [IsScalarTower R ℂ B] [AlgHomClass F ℂ A B] (φ : F) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hφ : Continuous φ := by fun_prop) (ha : p a := by cfc_tac) (hφa : q (φ a) := by cfc_tac) :
    φ (cfc f a) = cfc f (φ a) :=
  StarAlgHomClass.map_cfc (S := ℂ) φ f a

end MapCFC

section MapCFCₙ

variable {F R A B : Type*} {p : A → Prop} {q : B → Prop}
  [CommRing R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalRing R]
  [ContinuousStar R]
  [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalRing B] [StarRing B] [TopologicalSpace B] [Module R B]
  [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalContinuousFunctionalCalculus R A p] [NonUnitalContinuousFunctionalCalculus R B q]
  [ContinuousMapZero.UniqueHom R B] [FunLike F A B] [StarHomClass F A B]

/-- `NonUnitalStarAlgHomClass.map_cfcₙ` for an `R`-algebra homomorphism. Unlike the original, it
asks for `R` to be a ring, so it does not apply over `ℝ≥0`. -/
lemma NonUnitalStarAlgHomClass.map_cfcₙ' [NonUnitalAlgHomClass F R A B] (φ : F) (f : R → R)
    (a : A) (hf : ContinuousOn f (quasispectrum R a) := by cfc_cont_tac)
    (hf₀ : f 0 = 0 := by cfc_zero_tac) (hφ : Continuous φ := by fun_prop) (ha : p a := by cfc_tac)
    (hφa : q (φ a) := by cfc_tac) : φ (cfcₙ f a) = cfcₙ f (φ a) :=
  NonUnitalStarAlgHomClass.map_cfcₙ (S := R) φ f a

end MapCFCₙ

section MapCFCₙComplex

variable {F R A B : Type*} {p : A → Prop} {q : B → Prop}
  [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
  [ContinuousStar R]
  [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalRing B] [StarRing B] [TopologicalSpace B] [Module R B]
  [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalContinuousFunctionalCalculus R A p] [NonUnitalContinuousFunctionalCalculus R B q]
  [ContinuousMapZero.UniqueHom R B] [FunLike F A B] [StarHomClass F A B]

/-- `NonUnitalStarAlgHomClass.map_cfcₙ` for a `ℂ`-algebra homomorphism. -/
lemma NonUnitalStarAlgHomClass.map_cfcₙ_complex [Algebra R ℂ] [Module ℂ A] [Module ℂ B]
    [IsScalarTower R ℂ A] [IsScalarTower R ℂ B] [NonUnitalAlgHomClass F ℂ A B] (φ : F)
    (f : R → R) (a : A) (hf : ContinuousOn f (quasispectrum R a) := by cfc_cont_tac)
    (hf₀ : f 0 = 0 := by cfc_zero_tac) (hφ : Continuous φ := by fun_prop) (ha : p a := by cfc_tac)
    (hφa : q (φ a) := by cfc_tac) : φ (cfcₙ f a) = cfcₙ f (φ a) :=
  NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) φ f a

end MapCFCₙComplex

section MapProd

variable {A B R : Type*} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [StarRing A] [StarRing B] [TopologicalSpace A] [TopologicalSpace B] {pab : A × B → Prop}
  {pa : A → Prop} {pb : B → Prop}
  [ContinuousFunctionalCalculus R (A × B) pab]
  [ContinuousFunctionalCalculus R A pa] [ContinuousFunctionalCalculus R B pb]
  [ContinuousMap.UniqueHom R A] [ContinuousMap.UniqueHom R B]

/-- `cfc_map_prod` without its ring `S`, which is `R` itself here. -/
lemma cfc_map_prod' (f : R → R) (a : A) (b : B)
    (hf : ContinuousOn f (spectrum R a ∪ spectrum R b) := by cfc_cont_tac)
    (hab : pab (a, b) := by cfc_tac) (ha : pa a := by cfc_tac) (hb : pb b := by cfc_tac) :
    cfc f (a, b) = (cfc f a, cfc f b) := by
  ext
  case fst =>
    exact (StarAlgHom.fst R A B).map_cfc f (a, b) (by rwa [Prod.spectrum_eq]) continuous_fst hab ha
  case snd =>
    exact (StarAlgHom.snd R A B).map_cfc f (a, b) (by rwa [Prod.spectrum_eq]) continuous_snd hab hb

end MapProd

section MapProdNonUnital

variable {A B R : Type*} [CommRing R] [Nontrivial R] [StarRing R]
  [MetricSpace R] [IsTopologicalRing R] [ContinuousStar R] [NonUnitalRing A]
  [NonUnitalRing B] [Module R A] [Module R B]
  [SMulCommClass R A A] [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B]
  [StarRing A] [StarRing B] [TopologicalSpace A] [TopologicalSpace B]
  {pab : A × B → Prop} {pa : A → Prop} {pb : B → Prop}
  [NonUnitalContinuousFunctionalCalculus R (A × B) pab]
  [NonUnitalContinuousFunctionalCalculus R A pa]
  [NonUnitalContinuousFunctionalCalculus R B pb]
  [ContinuousMapZero.UniqueHom R A] [ContinuousMapZero.UniqueHom R B]

/-- `cfcₙ_map_prod` at `S := R`. Unlike the original, it asks for `R` to be a ring, so it does not
apply over `ℝ≥0`. -/
lemma cfcₙ_map_prod' (f : R → R) (a : A) (b : B)
    (hf : ContinuousOn f (quasispectrum R a ∪ quasispectrum R b) := by cfc_cont_tac)
    (hab : pab (a, b) := by cfc_tac) (ha : pa a := by cfc_tac) (hb : pb b := by cfc_tac) :
    cfcₙ f (a, b) = (cfcₙ f a, cfcₙ f b) :=
  cfcₙ_map_prod (S := R) f a b

end MapProdNonUnital

section MapProdNonUnitalComplex

variable {A B R : Type*} [CommSemiring R] [Nontrivial R] [StarRing R]
  [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
  [NonUnitalRing B] [Module R A] [Module R B]
  [SMulCommClass R A A] [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B]
  [StarRing A] [StarRing B] [TopologicalSpace A] [TopologicalSpace B]
  {pab : A × B → Prop} {pa : A → Prop} {pb : B → Prop}
  [NonUnitalContinuousFunctionalCalculus R (A × B) pab]
  [NonUnitalContinuousFunctionalCalculus R A pa]
  [NonUnitalContinuousFunctionalCalculus R B pb]
  [ContinuousMapZero.UniqueHom R A] [ContinuousMapZero.UniqueHom R B]

/-- `cfcₙ_map_prod` at `S := ℂ`. -/
lemma cfcₙ_map_prod_complex [Algebra R ℂ] [Module ℂ A] [Module ℂ B] [IsScalarTower R ℂ A]
    [IsScalarTower R ℂ B] (f : R → R) (a : A) (b : B)
    (hf : ContinuousOn f (quasispectrum R a ∪ quasispectrum R b) := by cfc_cont_tac)
    (hab : pab (a, b) := by cfc_tac) (ha : pa a := by cfc_tac) (hb : pb b := by cfc_tac) :
    cfcₙ f (a, b) = (cfcₙ f a, cfcₙ f b) :=
  cfcₙ_map_prod (S := ℂ) f a b

end MapProdNonUnitalComplex

namespace CFC

section Quasispectrum

-- TODO: these two results and the `grind` pattern should move next to
-- `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`.

lemma quasispectrum_nonpos_of_nonpos {𝕜 A : Type*} [CommRing 𝕜]
    [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [NonUnitalRing A] [PartialOrder A]
    [IsOrderedAddMonoid A] [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] (a : A) (ha : a ≤ 0) :
    ∀ x ∈ quasispectrum 𝕜 a, x ≤ 0 := by
  have := quasispectrum_nonneg_of_nonneg (𝕜 := 𝕜) (-a) (by simpa using ha)
  simpa [Unitization.quasispectrum_eq_spectrum_inr 𝕜, ← spectrum.neg_eq]

lemma nonpos_of_mem_quasispectrum {𝕜 A : Type*} [CommRing 𝕜]
    [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [NonUnitalRing A] [PartialOrder A]
    [IsOrderedAddMonoid A] [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {a : A} (ha : a ≤ 0) {x : 𝕜}
    (hx : x ∈ quasispectrum 𝕜 a) : x ≤ 0 := quasispectrum_nonpos_of_nonpos a ha x hx

grind_pattern nonpos_of_mem_quasispectrum => x ∈ quasispectrum 𝕜 a

end Quasispectrum

section Sqrt

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

lemma sqrt_def (a : A) : sqrt a = cfcₙ NNReal.sqrt a := rfl

lemma abs_def (a : A) : abs a = cfcₙ NNReal.sqrt (star a * a) := rfl

end Sqrt

section Log

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma log_def (a : A) : log a = cfc Real.log a := rfl

end Log

end CFC

section Norm

open CFC
open scoped ComplexOrder

section Unital

variable {A : Type*}
  [Ring A] [TopologicalSpace A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [IsTopologicalRing A] [T2Space A]

lemma cfc_real_comp_norm [Algebra ℝ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] (f : ℝ → ℝ) (a : A)
    (ha : IsSelfAdjoint a := by cfc_tac)
    (hf : ContinuousOn f ((‖·‖) '' spectrum ℝ a) := by cfc_cont_tac) :
    cfc (f ‖·‖) a = cfc f (abs a) :=
  cfc_comp_norm f a

lemma cfc_complex_comp_norm [Algebra ℂ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℂ A IsStarNormal] (f : ℂ → ℂ) (a : A)
    (ha : IsStarNormal a := by cfc_tac)
    (hf : ContinuousOn f ((‖·‖) '' spectrum ℂ a) := by cfc_cont_tac) :
    cfc (f ‖·‖) a = cfc f (abs a) :=
  cfc_comp_norm f a

/-- `CFC.abs_eq_cfcₙ_coe_norm` at `ℂ`, with the coercion `ℝ → ℂ` as it elaborates at `ℂ`, and the
unital calculus. -/
lemma CFC.abs_eq_cfc_complex_norm [Algebra ℂ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℂ A IsStarNormal] (a : A)
    (ha : IsStarNormal a := by cfc_tac) :
    abs a = cfc (fun x : ℂ ↦ (‖x‖ : ℂ)) a :=
  -- a term, as the two coercions are only equal at default transparency
  (abs_eq_cfcₙ_coe_norm ℂ a ha).trans cfcₙ_eq_cfc

end Unital

section NonUnital

variable {A : Type*} [NonUnitalRing A] [TopologicalSpace A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [IsTopologicalRing A] [T2Space A]

lemma cfcₙ_real_comp_norm [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonnegSpectrumClass ℝ A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (f : ℝ → ℝ) (a : A)
    (ha : IsSelfAdjoint a := by cfc_tac)
    (hf : ContinuousOn f ((‖·‖) '' quasispectrum ℝ a) := by cfc_cont_tac) :
    cfcₙ (f ‖·‖) a = cfcₙ f (abs a) :=
  cfcₙ_comp_norm f a

lemma cfcₙ_complex_comp_norm [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    [NonnegSpectrumClass ℝ A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]
    (f : ℂ → ℂ) (a : A)
    (ha : IsStarNormal a := by cfc_tac)
    (hf : ContinuousOn f ((‖·‖) '' quasispectrum ℂ a) := by cfc_cont_tac) :
    cfcₙ (f ‖·‖) a = cfcₙ f (abs a) :=
  cfcₙ_comp_norm f a

/-- `CFC.abs_eq_cfcₙ_coe_norm` at `ℂ`, with the coercion `ℝ → ℂ` as it elaborates at `ℂ`. -/
lemma CFC.abs_eq_cfcₙ_complex_norm [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    [NonnegSpectrumClass ℝ A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal] (a : A)
    (ha : IsStarNormal a := by cfc_tac) :
    abs a = cfcₙ (fun x : ℂ ↦ (‖x‖ : ℂ)) a :=
  abs_eq_cfcₙ_coe_norm ℂ a ha

end NonUnital

end Norm

@[fun_prop]
lemma StarAlgHom.continuous_restrictScalars {R S A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S]
    [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B] [IsScalarTower R S A]
    [IsScalarTower R S B] [Star A] [Star B] {f : A →⋆ₐ[S] B} (hf : Continuous f) :
    Continuous (f.restrictScalars R) :=
  hf
