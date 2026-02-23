/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Ideals
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Gelfand Duality

The `gelfandTransform` is an algebra homomorphism from a topological `𝕜`-algebra `A` to
`C(characterSpace 𝕜 A, 𝕜)`. In the case where `A` is a commutative complex Banach algebra, then
the Gelfand transform is actually spectrum-preserving (`spectrum.gelfandTransform_eq`). Moreover,
when `A` is a commutative C⋆-algebra over `ℂ`, then the Gelfand transform is a surjective isometry,
and even an equivalence between C⋆-algebras.

Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η₁ : id → F ∘ G := gelfandStarTransform` and
`η₂ : id → G ∘ F := WeakDual.CharacterSpace.homeoEval` are the natural isomorphisms implementing
**Gelfand Duality**, i.e., the (contravariant) equivalence of these categories.

## Main definitions

* `Ideal.toCharacterSpace` : constructs an element of the character space from a maximal ideal in
  a commutative complex Banach algebra
* `WeakDual.CharacterSpace.compContinuousMap`: The functorial map taking `ψ : A →⋆ₐ[𝕜] B` to a
  continuous function `characterSpace 𝕜 B → characterSpace 𝕜 A` given by pre-composition with `ψ`.

## Main statements

* `spectrum.gelfandTransform_eq` : the Gelfand transform is spectrum-preserving when the algebra is
  a commutative complex Banach algebra.
* `gelfandTransform_isometry` : the Gelfand transform is an isometry when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandTransform_bijective` : the Gelfand transform is bijective when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandStarTransform_naturality`: The `gelfandStarTransform` is a natural isomorphism
* `WeakDual.CharacterSpace.homeoEval_naturality`: This map implements a natural isomorphism

## TODO

* After defining the category of commutative unital C⋆-algebras, bundle the existing unbundled
  **Gelfand duality** into an actual equivalence (duality) of categories associated to the
  functors `C(·, ℂ)` and `characterSpace ℂ ·` and the natural isomorphisms `gelfandStarTransform`
  and `WeakDual.CharacterSpace.homeoEval`.

## Tags

Gelfand transform, character space, C⋆-algebra
-/

@[expose] public section

namespace StarAlgEquiv

section NonUnital

variable {R A₁ A₂ A₃ A₁' A₂' A₃' : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A₁] [DistribMulAction R A₁] [Star A₁]
  [NonUnitalNonAssocSemiring A₂] [DistribMulAction R A₂] [Star A₂]
  [NonUnitalNonAssocSemiring A₃] [DistribMulAction R A₃] [Star A₃]
  [NonUnitalNonAssocSemiring A₁'] [DistribMulAction R A₁'] [Star A₁']
  [NonUnitalNonAssocSemiring A₂'] [DistribMulAction R A₂'] [Star A₂']
  [NonUnitalNonAssocSemiring A₃'] [DistribMulAction R A₃'] [Star A₃']
  (e : A₁ ≃⋆ₐ[R] A₂)

/-- Reintrepret a star algebra equivalence as a non-unital star algebra homomorphism. -/
@[simps]
def toNonUnitalStarAlgHom : A₁ →⋆ₙₐ[R] A₂ where
  toFun := e
  map_add' := map_add e
  map_zero' := map_zero e
  map_mul' := map_mul e
  map_smul' := map_smul e
  map_star' := map_star e

@[simp]
lemma toNonUnitalStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toNonUnitalStarAlgHom.comp e₁.toNonUnitalStarAlgHom =
      (e₁.trans e₂).toNonUnitalStarAlgHom := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
@[simps apply]
def arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (A₁ →⋆ₙₐ[R] A₂) ≃ (A₁' →⋆ₙₐ[R] A₂') where
  toFun f := (e₂.toNonUnitalStarAlgHom.comp f).comp e₁.symm.toNonUnitalStarAlgHom
  invFun f := (e₂.symm.toNonUnitalStarAlgHom.comp f).comp e₁.toNonUnitalStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

theorem arrowCongr'_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ →⋆ₙₐ[R] A₂) (g : A₂ →⋆ₙₐ[R] A₃) :
    arrowCongr' e₁ e₃ (g.comp f) = (arrowCongr' e₂ e₃ g).comp (arrowCongr' e₁ e₂ f) := by
  ext
  simp

@[simp]
theorem arrowCongr'_refl : arrowCongr' .refl .refl = Equiv.refl (A₁ →⋆ₙₐ[R] A₂) :=
  rfl

@[simp]
theorem arrowCongr'_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

@[simp]
theorem arrowCongr'_symm (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm :=
  rfl

/-- Construct a star algebra equivalence from a pair of non-unital star algebra homomorphisms. -/
@[simps]
def ofHomInv' {R A B : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] A) (h₁ : g.comp f = .id R A) (h₂ : f.comp g = .id R B) :
    A ≃⋆ₐ[R] B where
  toFun := f
  invFun := g
  left_inv x := congr($h₁ x)
  right_inv x := congr($h₂ x)
  map_mul' := map_mul f
  map_add' := map_add f
  map_star' := map_star f
  map_smul' := map_smul f

end NonUnital

end StarAlgEquiv


open WeakDual

open scoped NNReal

section ComplexBanachAlgebra

open Ideal

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (I : Ideal A)
  [Ideal.IsMaximal I]

/-- Every maximal ideal in a commutative complex Banach algebra gives rise to a character on that
algebra. In particular, the character, which may be identified as an algebra homomorphism due to
`WeakDual.CharacterSpace.equivAlgHom`, is given by the composition of the quotient map and
the Gelfand-Mazur isomorphism `NormedRing.algEquivComplexOfComplete`. -/
noncomputable def Ideal.toCharacterSpace : characterSpace ℂ A :=
  CharacterSpace.equivAlgHom.symm <|
    ((NormedRing.algEquivComplexOfComplete
      (letI := Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm : A ⧸ I →ₐ[ℂ] ℂ).comp <|
    Quotient.mkₐ ℂ I

set_option backward.isDefEq.respectTransparency false in
theorem Ideal.toCharacterSpace_apply_eq_zero_of_mem {a : A} (ha : a ∈ I) :
    I.toCharacterSpace a = 0 := by
  unfold Ideal.toCharacterSpace
  simp only [CharacterSpace.equivAlgHom_symm_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    Quotient.mkₐ_eq_mk, Function.comp_apply, NormedRing.algEquivComplexOfComplete_symm_apply]
  simp_rw [Quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq]
  exact Set.eq_of_mem_singleton (Set.singleton_nonempty (0 : ℂ)).some_mem

/-- If `a : A` is not a unit, then some character takes the value zero at `a`. This is equivalent
to `gelfandTransform ℂ A a` takes the value zero at some character. -/
theorem WeakDual.CharacterSpace.exists_apply_eq_zero {a : A} (ha : ¬IsUnit a) :
    ∃ f : characterSpace ℂ A, f a = 0 := by
  obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha)
  exact
    ⟨M.toCharacterSpace,
      M.toCharacterSpace_apply_eq_zero_of_mem
        (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩

theorem WeakDual.CharacterSpace.mem_spectrum_iff_exists {a : A} {z : ℂ} :
    z ∈ spectrum ℂ a ↔ ∃ f : characterSpace ℂ A, f a = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨f, hf⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hz
    simp only [map_sub, sub_eq_zero, AlgHomClass.commutes] at hf
    exact ⟨_, hf.symm⟩
  · rintro ⟨f, rfl⟩
    exact AlgHom.apply_mem_spectrum f a

/-- The Gelfand transform is spectrum-preserving. -/
theorem spectrum.gelfandTransform_eq (a : A) :
    spectrum ℂ (gelfandTransform ℂ A a) = spectrum ℂ a := by
  ext z
  rw [ContinuousMap.spectrum_eq_range, WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  exact Iff.rfl

instance [Nontrivial A] : Nonempty (characterSpace ℂ A) :=
  ⟨Classical.choose <|
      WeakDual.CharacterSpace.exists_apply_eq_zero <| zero_mem_nonunits.2 zero_ne_one⟩

end ComplexBanachAlgebra

section ComplexCStarAlgebra

variable {A : Type*} [CommCStarAlgebra A]

theorem gelfandTransform_map_star (a : A) :
    gelfandTransform ℂ A (star a) = star (gelfandTransform ℂ A a) :=
  ContinuousMap.ext fun φ => map_star φ a

variable (A)

/-- The Gelfand transform is an isometry when the algebra is a C⋆-algebra over `ℂ`. -/
theorem gelfandTransform_isometry : Isometry (gelfandTransform ℂ A) := by
  refine AddMonoidHomClass.isometry_of_norm (gelfandTransform ℂ A) fun a => ?_
  /- By `spectrum.gelfandTransform_eq`, the spectra of `star a * a` and its
    `gelfandTransform` coincide. Therefore, so do their spectral radii, and since they are
    self-adjoint, so also do their norms. Applying the C⋆-property of the norm and taking square
    roots shows that the norm is preserved. -/
  have : spectralRadius ℂ (gelfandTransform ℂ A (star a * a)) = spectralRadius ℂ (star a * a) := by
    unfold spectralRadius; rw [spectrum.gelfandTransform_eq]
  rw [map_mul, (IsSelfAdjoint.star_mul_self a).spectralRadius_eq_nnnorm, gelfandTransform_map_star,
    (IsSelfAdjoint.star_mul_self (gelfandTransform ℂ A a)).spectralRadius_eq_nnnorm] at this
  simp only [ENNReal.coe_inj, CStarRing.nnnorm_star_mul_self, ← sq] at this
  simpa only [Function.comp_apply, NNReal.sqrt_sq] using
    congr_arg (((↑) : ℝ≥0 → ℝ) ∘ ⇑NNReal.sqrt) this

set_option backward.isDefEq.respectTransparency false in
/-- The Gelfand transform is bijective when the algebra is a C⋆-algebra over `ℂ`. -/
theorem gelfandTransform_bijective : Function.Bijective (gelfandTransform ℂ A) := by
  refine ⟨(gelfandTransform_isometry A).injective, ?_⟩
  /- The range of `gelfandTransform ℂ A` is actually a `StarSubalgebra`. The key lemma below may be
    hard to spot; it's `map_star` coming from `WeakDual.Complex.instStarHomClass`, which is a
    nontrivial result. -/
  let rng : StarSubalgebra ℂ C(characterSpace ℂ A, ℂ) :=
    { toSubalgebra := (gelfandTransform ℂ A).range
      star_mem' := by
        rintro - ⟨a, rfl⟩
        use star a
        ext1 φ
        dsimp
        simp only [map_star, RCLike.star_def] }
  suffices rng = ⊤ from
    fun x => show x ∈ rng from this.symm ▸ StarSubalgebra.mem_top
  /- Because the `gelfandTransform ℂ A` is an isometry, it has closed range, and so by the
    Stone-Weierstrass theorem, it suffices to show that the image of the Gelfand transform separates
    points in `C(characterSpace ℂ A, ℂ)` and is closed under `star`. -/
  have h : rng.topologicalClosure = rng := le_antisymm
    (StarSubalgebra.topologicalClosure_minimal le_rfl
      (gelfandTransform_isometry A).isClosedEmbedding.isClosed_range)
    (StarSubalgebra.le_topologicalClosure _)
  refine h ▸ ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    _ (fun _ _ => ?_)
  /- Separating points just means that elements of the `characterSpace` which agree at all points
    of `A` are the same functional, which is just extensionality. -/
  contrapose!
  exact fun h => Subtype.ext (ContinuousLinearMap.ext fun a =>
    h (gelfandTransform ℂ A a) ⟨gelfandTransform ℂ A a, ⟨a, rfl⟩, rfl⟩)

/-- The Gelfand transform as a `StarAlgEquiv` between a commutative unital C⋆-algebra over `ℂ`
and the continuous functions on its `characterSpace`. -/
@[simps!]
noncomputable def gelfandStarTransform : A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) :=
  StarAlgEquiv.ofBijective
    (show A →⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) from
      { gelfandTransform ℂ A with map_star' := fun x => gelfandTransform_map_star x })
    (gelfandTransform_bijective A)

end ComplexCStarAlgebra

section NonUnitalCStarAlgebra

/-- The element of `WeakDual.characterSpace` on `Unitization 𝕜 A` corresponding to the
algebra homomorphism consisting of projection onto the scalar part.

When `A` is a C⋆-algebra composing the inclusion map `A → A⁺¹` with the Gelfand transform
`A⁺¹ → C(characterSpace ℂ A⁺¹, ℂ)`, is an injective non-unital star homomorphism whose range is
precisely kernel of the evaluation map at this point. -/
noncomputable def CharacterSpace.pt (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NonUnitalNormedRing A] [CompleteSpace A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [RegularNormedAlgebra 𝕜 A] :
    characterSpace 𝕜 (Unitization 𝕜 A) :=
  CharacterSpace.equivAlgHom.symm <| Unitization.fstHom 𝕜 A

@[simps!]
def _root_.NonUnitalAlgHom.toStrongDual {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [CompleteSpace A] [CompleteSpace 𝕜] [RegularNormedAlgebra 𝕜 A] (φ : A →ₙₐ[𝕜] 𝕜) :
    StrongDual 𝕜 A where
  toLinearMap := (φ : A →ₗ[𝕜] 𝕜)
  cont := by
    convert map_continuous (Unitization.lift φ) |>.comp Unitization.continuous_inr
    simp [Function.comp_def]

@[simps]
def WeakDual.characterSpace.equivNonUnitalAlgHomSubtype (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [CompleteSpace A] [CompleteSpace 𝕜] [RegularNormedAlgebra 𝕜 A] :
    characterSpace 𝕜 A ≃ {φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0} where
  toFun φ :=
    { val := CharacterSpace.toNonUnitalAlgHom φ
      property := by simpa [DFunLike.ext'_iff] using φ.prop.1 }
  invFun φ :=
    ⟨φ.val.toStrongDual.toWeakDual, by simpa [DFunLike.ext_iff] using φ.prop, map_mul φ.val⟩
  left_inv φ := by ext; rfl
  right_inv φ := by ext; rfl

lemma Unitization.lift_zero {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] {C : Type*} [Semiring C] [Algebra R C] :
    Unitization.lift (0 : A →ₙₐ[R] C) = (Algebra.ofId R C).comp (Unitization.fstHom R A) := by
  ext x
  change (0 : A →ₙₐ[R] C).toAlgHom x = algebraMap R C (x : Unitization R A).fst -- wut?
  simp

open Unitization in
noncomputable def CharacterSpace.equivSubtypeNePt {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [CompleteSpace A] [CompleteSpace 𝕜] [RegularNormedAlgebra 𝕜 A] :
    characterSpace 𝕜 A ≃ {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ CharacterSpace.pt 𝕜 A} :=
  letI e₁ := characterSpace.equivNonUnitalAlgHomSubtype 𝕜 A
  letI e₂ : {φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0} ≃ {φ : Unitization 𝕜 A →ₐ[𝕜] 𝕜 // φ ≠ fstHom 𝕜 A} :=
    lift.subtypeEquiv fun φ ↦ by
      simp only [ne_eq, not_iff_not]
      constructor
      · rintro rfl
        simp only [Unitization.lift_zero, Algebra.ofId_self, AlgHom.id_comp]
      · intro hφ
        simpa [-lift_apply] using congr(lift.symm $hφ)
  letI e₃ : {φ : Unitization 𝕜 A →ₐ[𝕜] 𝕜 // φ ≠ fstHom 𝕜 A} ≃
      {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ CharacterSpace.pt 𝕜 A} :=
    CharacterSpace.equivAlgHom.symm.subtypeEquiv fun φ ↦ by
      simp only [ne_eq, not_iff_not]
      constructor
      · rintro rfl
        rfl
      · intro hφ
        simpa [CharacterSpace.pt] using congr(CharacterSpace.equivAlgHom $hφ)
  (e₁.trans e₂).trans e₃

noncomputable def CharacterSpace.homeomorphSubtypeNePt {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [CompleteSpace A] [CompleteSpace 𝕜] [RegularNormedAlgebra 𝕜 A] :
    characterSpace 𝕜 A ≃ₜ
      {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ CharacterSpace.pt 𝕜 A} where
  toEquiv := CharacterSpace.equivSubtypeNePt
  continuous_toFun := by
    rw [continuous_induced_rng, continuous_induced_rng]
    apply WeakDual.continuous_of_continuous_eval fun a ↦ ?_
    induction a using Unitization.ind with
    | inl_add_inr r a =>
      convert_to Continuous fun φ : characterSpace 𝕜 A ↦ r + φ a
      · ext φ
        simp [equivSubtypeNePt]
      · exact continuous_const.add <| (eval_continuous a).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    apply WeakDual.continuous_of_continuous_eval fun a ↦ ?_
    convert ((eval_continuous _).comp continuous_subtype_val).comp continuous_subtype_val

open CStarAlgebra Unitization in
example {A : Type*} [NonUnitalCommCStarAlgebra A] : False := by
  let g := gelfandStarTransform A⁺¹
  let i := inrNonUnitalStarAlgHom ℂ A
  have φ : A →⋆ₙₐ[ℂ] C(characterSpace ℂ A⁺¹, ℂ) := StarAlgEquiv.arrowCongr' .refl g i
  sorry

end NonUnitalCStarAlgebra
section Functoriality

namespace WeakDual

namespace CharacterSpace

variable {A B C 𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [StarRing A]
variable [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] [StarRing B]
variable [NormedRing C] [NormedAlgebra 𝕜 C] [CompleteSpace C] [StarRing C]

/-- The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a continuous function
`characterSpace ℂ B → characterSpace ℂ A` obtained by pre-composition with `ψ`. -/
@[simps]
noncomputable def compContinuousMap (ψ : A →⋆ₐ[𝕜] B) :
    C(characterSpace 𝕜 B, characterSpace 𝕜 A) where
  toFun φ := equivAlgHom.symm ((equivAlgHom φ).comp ψ.toAlgHom)
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform 𝕜 B (ψ a)) _

variable (A) in
/-- `WeakDual.CharacterSpace.compContinuousMap` sends the identity to the identity. -/
@[simp]
theorem compContinuousMap_id :
    compContinuousMap (StarAlgHom.id 𝕜 A) = ContinuousMap.id (characterSpace 𝕜 A) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl

/-- `WeakDual.CharacterSpace.compContinuousMap` is functorial. -/
@[simp]
theorem compContinuousMap_comp (ψ₂ : B →⋆ₐ[𝕜] C) (ψ₁ : A →⋆ₐ[𝕜] B) :
    compContinuousMap (ψ₂.comp ψ₁) = (compContinuousMap ψ₁).comp (compContinuousMap ψ₂) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl

end CharacterSpace

end WeakDual

end Functoriality

open CharacterSpace in
/--
Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η : id → F ∘ G := gelfandStarTransform` is a natural isomorphism implementing (half of)
the duality between these categories. That is, for commutative unital C⋆-algebras `A` and `B` and
`φ : A →⋆ₐ[ℂ] B` the following diagram commutes:

```
A  --- η A ---> C(characterSpace ℂ A, ℂ)

|                     |

φ                  (F ∘ G) φ

|                     |
V                     V

B  --- η B ---> C(characterSpace ℂ B, ℂ)
```
-/
theorem gelfandStarTransform_naturality {A B : Type*} [CommCStarAlgebra A] [CommCStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) :
    (gelfandStarTransform B : _ →⋆ₐ[ℂ] _).comp φ =
      (compContinuousMap φ |>.compStarAlgHom' ℂ ℂ).comp (gelfandStarTransform A : _ →⋆ₐ[ℂ] _) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η : id → G ∘ F := WeakDual.CharacterSpace.homeoEval` is a natural isomorphism implementing
(half of) the duality between these categories. That is, for compact Hausdorff spaces `X` and `Y`,
`f : C(X, Y)` the following diagram commutes:

```
X  --- η X ---> characterSpace ℂ C(X, ℂ)

|                     |

f                  (G ∘ F) f

|                     |
V                     V

Y  --- η Y ---> characterSpace ℂ C(Y, ℂ)
```
-/
lemma WeakDual.CharacterSpace.homeoEval_naturality {X Y 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (f : C(X, Y)) :
    (homeoEval Y 𝕜 : C(_, _)).comp f =
      (f.compStarAlgHom' 𝕜 𝕜 |> compContinuousMap).comp (homeoEval X 𝕜 : C(_, _)) :=
  rfl
