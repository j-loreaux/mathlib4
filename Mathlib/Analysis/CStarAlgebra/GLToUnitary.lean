import Mathlib
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-! # Relationships between invertibility and nonnegative elements
## Main definitions
+ `unitOfAddNonneg`: the unit obtained by adding a positive scalar to a nonnegative
  element in a C⋆-algebra.
-/

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [TopologicalSpace A] [Algebra ℝ A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

open scoped NNReal

namespace CFC

/-- The unit obtained by adding a positive scalar to a nonnegative element in a C⋆-algebra. -/
noncomputable def unitOfAddNonneg {r : ℝ} (hr : 0 < r) (a : A) (ha : 0 ≤ a := by cfc_tac) : Aˣ :=
  cfcUnits (r + ·) a (by grind) (by fun_prop)

variable {r : ℝ} {hr : 0 < r} {a : A} {ha : 0 ≤ a}

/-- This is not marked as a `simp` lemma because there may be several rewrite options that are
preferable. -/
lemma val_unitOfAddNonneg :
    (unitOfAddNonneg hr a ha : A) = cfc (r + ·) a := by
  rfl

/-- This is not marked as a `simp` lemma because there may be several rewrite options that are
preferable. -/
lemma val_inv_unitOfAddNonneg :
    (↑(unitOfAddNonneg hr a ha)⁻¹ : A) = cfc (fun x ↦ (r + x)⁻¹) a := by
  rfl

lemma val_unitOfAddNonneg_eq_algebraMap_add_self :
    (unitOfAddNonneg hr a ha : A) = algebraMap ℝ A r + a := by
  rw [val_unitOfAddNonneg, cfc_add .., cfc_id' .., cfc_const ..]

@[simp]
lemma val_unitOfAddNonneg_nonneg : 0 ≤ (unitOfAddNonneg hr a ha : A) :=
  cfc_nonneg <| by grind

@[simp]
lemma val_inv_unitOfAddNonneg_nonneg : 0 ≤ (↑(unitOfAddNonneg hr a ha)⁻¹ : A) :=
  cfc_nonneg <| fun _ _ ↦ _root_.inv_nonneg.mpr <| by grind

lemma le_val_unitOfAddNonneg : algebraMap ℝ A r ≤ unitOfAddNonneg hr a ha := by
  rw [← add_zero (algebraMap _ _ r), val_unitOfAddNonneg_eq_algebraMap_add_self]
  gcongr

lemma val_inv_unitOfAddNonneg_le : (↑(unitOfAddNonneg hr a ha)⁻¹ : A) ≤ algebraMap ℝ A r⁻¹ := by
  rw [val_inv_unitOfAddNonneg, le_algebraMap_iff_spectrum_le, cfc_map_spectrum _ _ (hf := ?_)]
  · rintro - ⟨x, hx, rfl⟩
    replace hx := spectrum_nonneg_of_nonneg ha hx
    rw [inv_le_inv₀ (by positivity) hr]
    exact le_add_of_nonneg_right hx
  · exact ContinuousOn.inv₀ (by fun_prop) (by grind)

@[simp]
lemma IsStrictlyPositive.unitOfAddNonneg : IsStrictlyPositive (unitOfAddNonneg hr a ha : A) := by
  simp [IsStrictlyPositive.iff_of_unital]

variable [IsTopologicalRing A] [T2Space A]

lemma val_unitOfAddNonneg_eq_cfc_nnreal {r : ℝ≥0} (hr : 0 < r) :
    (unitOfAddNonneg hr a ha : A) = cfc (r + ·) a := by
  rw [val_unitOfAddNonneg, cfc_nnreal_eq_real ..]
  apply cfc_congr fun x hx ↦ ?_
  simpa using spectrum_nonneg_of_nonneg ha hx

lemma val_inv_unitOfAddNonneg_eq_cfc_nnreal {r : ℝ≥0} (hr : 0 < r) :
    (↑(unitOfAddNonneg hr a ha)⁻¹ : A) = cfc (fun x ↦ (r + x)⁻¹) a := by
  rw [val_inv_unitOfAddNonneg, cfc_nnreal_eq_real ..]
  apply cfc_congr fun x hx ↦ ?_
  simpa using spectrum_nonneg_of_nonneg ha hx

end CFC

namespace CStarAlgebra
open CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {r : ℝ} {hr : 0 < r} {a : A} {ha : 0 ≤ a}

@[simp]
lemma norm_val_unitOfAddNonneg [Nontrivial A] {r : ℝ} {hr : 0 < r} {a : A} {ha : 0 ≤ a} :
    ‖(unitOfAddNonneg hr a ha : A)‖ = r + ‖a‖ := by
  lift r to ℝ≥0 using hr.le
  simp_rw [val_unitOfAddNonneg_eq_cfc_nnreal hr, ← coe_nnnorm]
  norm_cast
  apply IsGreatest.nnnorm_cfc_nnreal (r + ·) a |>.unique
  apply add_right_mono.map_isGreatest
  simpa [cfc_id ℝ≥0 a ha] using IsGreatest.nnnorm_cfc_nnreal id a

@[simp]
lemma nnnorm_val_unitOfAddNonneg [Nontrivial A] {r : ℝ≥0} {hr : 0 < r} {a : A} {ha : 0 ≤ a} :
    ‖(unitOfAddNonneg hr a ha : A)‖₊ = r + ‖a‖₊ :=
  Subtype.ext norm_val_unitOfAddNonneg

end CStarAlgebra

section Abs

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `CFC.abs a` as a unit of the algebra when `a` is a unit. -/
@[simps!]
noncomputable def CFC.absUnit (a : Aˣ) : Aˣ :=
  have key : ∀ x ∈ spectrum ℝ≥0 (star (a : A) * a), x ≠ 0 := by
      have : IsUnit (star (a : A) * a) := by aesop
      rintro - h rfl
      exact spectrum.zero_notMem ℝ≥0 this h
  Units.copy
    (cfcUnits NNReal.sqrt (star (a : A) * a) (by simpa using key) (by fun_prop))
    (CFC.abs (a : A))
    (by simp [CFC.abs, CFC.sqrt, cfcₙ_eq_cfc (f := NNReal.sqrt)])
    (cfc (·⁻¹ : ℝ≥0 → ℝ≥0) (abs a)) <| by
      simp only [val_inv_cfcUnits, CFC.abs]
      nth_rw 2 [cfc_comp' (hg := ?hg) ..]
      case hg =>
        apply continuousOn_id.inv₀
        simpa
      rw [CFC.sqrt_eq_cfc]

end Abs

section UnitsToUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The polar decomposition of a unit in a C⋆-algebra into a unitary and a
nonnegative unit. -/
@[simps!]
noncomputable def Units.polarDecomposition (a : Aˣ) : unitary A × Aˣ :=
  (⟨_, a.mul_inv_mem_unitary (CFC.absUnit a) |>.mpr <| Units.ext <| by
    simp [(CFC.abs_nonneg (a : A)).star_eq, CFC.abs_mul_abs]⟩,
    CFC.absUnit a)

lemma Units.polarDecomposition_mul (a : Aˣ) :
    (a.polarDecomposition.1 * a.polarDecomposition.2 : A) = a := by
  simpa using (CFC.absUnit a).inv_mul_cancel_right _

lemma Units.polarDecomposition_mul' (a : Aˣ) :
    unitary.toUnits a.polarDecomposition.1 * a.polarDecomposition.2 = a :=
  Units.ext a.polarDecomposition_mul

-- this can generalize a long way?
@[simp]
lemma unitary.cfcAbs_eq_one {u : A} (hu : u ∈ unitary A) :
    CFC.abs u = 1 := by
  rw [CFC.abs]
  convert CFC.sqrt_one (A := A) using 2
  exact star_mul_self_of_mem hu

@[simp]
lemma Units.polarDecomposition_unitary_toUnits (u : unitary A) :
    (unitary.toUnits u).polarDecomposition = (u, 1) := by
  ext <;> simp

lemma Units.polarDecomposition_of_nonneg (a : Aˣ) (ha : 0 ≤ (a : A) := by cfc_tac) :
    a.polarDecomposition = (1, a) := by
  ext
  · simp only [polarDecomposition_fst_coe, OneMemClass.coe_one]
    convert CFC.absUnit a |>.mul_inv
    ext
    simp [CFC.abs_of_nonneg (a : A)]
  · simp [CFC.abs_of_nonneg (a : A)]

-- this should go elsewhere and be more general
lemma cfc_inv_nnreal_eq_real (a : A) (ha : 0 ≤ a := by cfc_tac) :
    cfc (·⁻¹ : ℝ≥0 → ℝ≥0) a = cfc (·⁻¹ : ℝ → ℝ) a := by
  rw [cfc_nnreal_eq_real ..]
  apply cfc_congr fun x hx ↦ ?_
  simpa using spectrum_nonneg_of_nonneg ha hx

-- this should go elsewhere and be more general
omit [PartialOrder A] in
lemma cfc_inv_real_eq_complex (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc (·⁻¹ : ℝ → ℝ) a = cfc (·⁻¹ : ℂ → ℂ) a := by
  rw [cfc_real_eq_complex ..]
  apply cfc_congr fun x hx ↦ ?_
  simpa using ha.spectrumRestricts.rightInvOn hx

/-- A notation type class for `≪`, a notion of strict inequality.

Strict is the wrong word here. -/
class StrictLT (α : Type*) where
  llt : α → α → Prop

infix:50 "≪" => StrictLT.llt

instance : StrictLT A where
  llt x y := IsStrictlyPositive (y - x)

class StrictLTAddCommMonoid (α : Type*) [AddCommMonoid α] [PartialOrder α] [StrictLT α]
    extends CovariantClass α α (· + ·) (· ≪ ·) where
  lt_of_llt {x y : α} : x ≪ y → x ≤ y
  llt_of_le_of_llt {x y z : α} : x ≤ y → y ≪ z → x ≪ z
  llt_of_le_of_lt {x y z : α} : x ≤ y → y ≪ z → x ≪ z
  add_left_mono {x y z : α} : x ≪ y → z + x ≪ z + y

/-- The straight line path from `1` to `CFC.abs a` bundled within `Aˣ`.

See `Units.map_cfcAbsUnitPathToOne_val` for the statement the image of this path in `A`
is `Path.segment 1 (CFC.abs a)`. -/
@[simps!]
noncomputable def Units.cfcAbsUnitPathToOne (a : Aˣ) :
    Path (CFC.absUnit a) 1 where
  toContinuousMap := ContinuousMap.unitsOfForallIsUnit
    (f := ⟨fun t ↦ (1 - t : ℝ) • CFC.absUnit a + algebraMap ℝ A t, by fun_prop⟩) <| by
      intro t
      simp only [ContinuousMap.coe_mk]
      obtain rfl | ht := unitInterval.nonneg' (t := t) |>.eq_or_lt
      · simpa using (CFC.absUnit a).isUnit
      · replace ht : (0 : ℝ) < t := ht
        refine CStarAlgebra.isUnit_of_le ?_ ?_ (le_add_of_nonneg_left ?_)
        · exact IsUnit.map (algebraMap ℝ A) <| .mk0 _ ht.ne'
        · let e : ℝ →⋆ₐ[ℝ] A := ⟨Algebra.ofId ℝ A, by simp [← algebraMap_star_comm]⟩
          exact map_nonneg e ht.le
        · have ht' := unitInterval.le_one t
          exact smul_nonneg (by linarith) (by simp)
  source' := by ext; simp
  target' := by simp

lemma Units.map_cfcAbsUnitPathToOne_val (a : Aˣ) :
    a.cfcAbsUnitPathToOne.map continuous_val = .segment (CFC.abs (a : A)) 1 := by
  ext; simp [AffineMap.lineMap_apply_module, Algebra.algebraMap_eq_smul_one]

@[simps!]
noncomputable def Units.pathToPolarDecomposition (a : Aˣ) :
    Path a (unitary.toUnits a.polarDecomposition.1) :=
  Path.refl (unitary.toUnits a.polarDecomposition.1) |>.mul a.cfcAbsUnitPathToOne |>.cast
    a.polarDecomposition_mul'.symm (mul_one _).symm

instance {R : Type*} [NormedRing R] [HasSummableGeomSeries R] :
    IsOpenUnits R where
  isOpenEmbedding_unitsVal := Units.isOpenEmbedding_val

instance {M : Type*} [Monoid M] [TopologicalSpace M] [IsOpenUnits M] [LocPathConnectedSpace M] :
    LocPathConnectedSpace Mˣ :=
  IsOpenUnits.isOpenEmbedding_unitsVal.locPathConnectedSpace

lemma Units.continuous_val_comp_iff {α M : Type*}
    [TopologicalSpace α] [Monoid M] [TopologicalSpace M] [IsOpenUnits M] {f : α → Mˣ} :
    Continuous (val ∘ f) ↔ Continuous f :=
  IsOpenUnits.isOpenEmbedding_unitsVal.isInducing.continuous_iff.symm

example : LocPathConnectedSpace Aˣ := inferInstance

lemma PathConnectedSpace.of_joined {X : Type*} [TopologicalSpace X] (x : X)
    (h : ∀ y, Joined x y) : PathConnectedSpace X where
  nonempty := ⟨x⟩
  joined y z := h y |>.symm.trans <| h z

lemma CFC.continuousOn_sqrt : ContinuousOn (CFC.sqrt : A → A) {x | 0 ≤ x} := by
  -- We need the updated version of `ContinuousOn.cfcₙ_nnreal` to finish this proof
  -- Also, we should probably have a variant of that which
  -- uses upper hemicontinuity of the spectrum
  eta_expand
  simp_rw [CFC.sqrt]
  apply ContinuousOn.cfcₙ_nnreal
  · sorry
  · exact continuousOn_id
  · sorry
  · simp
  · sorry
  · sorry
  · sorry

@[fun_prop]
lemma CFC.continuous_abs : Continuous (CFC.abs : A → A) :=
  CFC.continuousOn_sqrt.comp_continuous (by fun_prop) (by aesop)

@[fun_prop]
lemma CFC.continuous_absUnit : Continuous (CFC.absUnit : Aˣ → Aˣ) := by
  simp [← Units.continuous_val_comp_iff, Function.comp_def]
  fun_prop

@[fun_prop]
lemma Units.continuous_polarDecomposition :
    Continuous (Units.polarDecomposition : Aˣ → unitary A × Aˣ) := by
  refine Continuous.prodMk ?_ (by fun_prop)
  rw [continuous_induced_rng]
  simp [Function.comp_def]
  apply Units.continuous_val.mul
  simp_rw [← CFC.val_absUnit]
  conv =>
    enter [1, x]
    rw [cfc_inv_id (CFC.absUnit x)]
  fun_prop

@[fun_prop]
lemma unitary.continuous_toUnits {M : Type*} [Monoid M] [StarMul M] [TopologicalSpace M]
    [ContinuousMul M] [ContinuousStar M] :
    Continuous (toUnits : unitary M → Mˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · simp only [Function.comp_def, val_toUnits_apply]
    fun_prop
  · simp only [val_inv_toUnits_apply]
    fun_prop

open ContinuousMap Prod Set unitary Units in
/-- The deformation retraction of `Aˣ` onto `unitary A` (more specifically, onto
`Set.range unitary.toUnits`) which sends `a : Aˣ` to the unitary from its polar decomposition.
along the path `Units.pathToPolarDecomposition`. -/
noncomputable def Units.deformationRetractionToUnitary :
    HomotopyRel (.id Aˣ) (⟨toUnits ∘ fst ∘ polarDecomposition, by fun_prop⟩) (range toUnits) where
  toFun ta := ta.2.pathToPolarDecomposition ta.1
  continuous_toFun := sorry
  map_zero_left a := by simp
  map_one_left a := by simp
  prop' := by
    rintro t - ⟨x, rfl⟩
    ext
    simp [sub_smul, Algebra.algebraMap_eq_smul_one]

end UnitsToUnitary

#exit

/-
a' - b'

a - b = a' * a' - b' * b' = a' * a' - a' * b' + a' * b' - b' * b
 = a' * (a' - b') + (a' - b') * b'
-/
