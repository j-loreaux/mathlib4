/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-!
# Hadamard's maximal determinant inequality

This file proves Hadamard's determinant bound for real matrices with entries bounded by one in
absolute value. It also characterizes equality in terms of `Matrix.IsHadamard`.

## Main results

* `Matrix.abs_det_le_sqrt_card_pow_card_of_abs_apply_le_one`: if `|A i j| ≤ 1`, then
  `|A.det| ≤ √ ((Fintype.card n : ℝ) ^ Fintype.card n)`.
* `Matrix.abs_det_eq_sqrt_card_pow_card_iff_isHadamard_of_abs_apply_le_one`: under the same
  entry bound, equality holds iff `A.IsHadamard`.
-/

@[expose] public section

open InnerProductSpace

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜]

lemma norm_det_eq_prod_abs_inner_gramSchmidt_rows
    [Fintype n] [DecidableEq n] [LinearOrder n]
    [LocallyFiniteOrderBot n] [WellFoundedLT n] (A : Matrix n n 𝕜) :
    letI v : n → EuclideanSpace 𝕜 n := fun i ↦ WithLp.toLp 2 (A i)
    ‖A.det‖ = ∏ i, ‖⟪gramSchmidtOrthonormalBasis finrank_euclideanSpace v i, v i⟫_𝕜‖ := by
  set v : n → EuclideanSpace 𝕜 n := fun i ↦ WithLp.toLp 2 (A i)
  set b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
    gramSchmidtOrthonormalBasis finrank_euclideanSpace v
  calc
    ‖A.det‖ = ‖b.toBasis.det (EuclideanSpace.basisFun n 𝕜) * A.det‖ := by
      simp [b.det_to_matrix_orthonormalBasis (EuclideanSpace.basisFun n 𝕜)]
    _ = ‖b.toBasis.det v‖ := by
      nth_rewrite 2 [(b.toBasis.det).eq_smul_basis_det (EuclideanSpace.basisFun n 𝕜).toBasis]
      simp [v, EuclideanSpace.basisFun_toBasis_det_toLp]
    _ = ∏ i, ‖⟪b i, v i⟫_𝕜‖ := by rw [gramSchmidtOrthonormalBasis_det, norm_prod]

private lemma euclidean_row_norm_sq_le_card
    [Fintype n] {A : Matrix n n 𝕜}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (i : n) :
    ‖(WithLp.toLp 2 (A i) : EuclideanSpace 𝕜 n)‖ ^ 2 ≤ (Fintype.card n : ℝ) := by
  suffices ∑ j, ‖A i j‖ ^ 2 ≤ ∑ j : n, (1 : ℝ) by simpa [EuclideanSpace.norm_sq_eq]
  gcongr
  grind [sq_le_one_iff_abs_le_one, abs_norm]

/-- There is another version of this theorem which assumes `∀ i ∈ s, 0 < f i` instead of
`∀ i ∈ s, 0 ≤ f i` and `0 < ∏ i ∈ s, g i`, but this is strictly more general. -/
theorem _root_.Finset.prod_eq_prod_iff_of_le_of_nonneg {ι M : Type*} [CommMonoidWithZero M]
    [PartialOrder M] [ZeroLEOneClass M] [PosMulStrictMono M] [Nontrivial M]
    {s : Finset ι} {f g : ι → M} (h : ∀ i ∈ s, f i ≤ g i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : 0 < ∏ i ∈ s, g i) :
    ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  refine ⟨?_, by congr! 1; grind⟩
  contrapose!
  rintro ⟨i, his, hi⟩
  replace hi : f i < g i := lt_of_le_of_ne (h i his) hi
  apply ne_of_lt
  by_cases! hf_pos : ∀ i ∈ s, 0 < f i
  · exact s.prod_lt_prod hf_pos h ⟨i, his, hi⟩
  · simp_rw [lt_iff_le_and_ne, not_and_or] at hf_pos
    obtain ⟨j, hj, hfj⟩ := hf_pos
    simpa [Finset.prod_eq_zero (f := f) hj (by grind)]

theorem _root_.Finset.prod_eq_prod_iff_of_le_of_pos {ι M : Type*} [CommMonoidWithZero M]
    [PartialOrder M] [ZeroLEOneClass M] [PosMulStrictMono M] [Nontrivial M]
    {s : Finset ι} {f g : ι → M} (h : ∀ i ∈ s, f i ≤ g i) (hf : ∀ i ∈ s, 0 < f i) :
    ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  refine Finset.prod_eq_prod_iff_of_le_of_nonneg h (by grind) ?_
  grw [Finset.prod_pos hf]
  gcongr <;> grind

open WithLp in
/-- **Hadamard's theorem on determinants**: The norm of the determinant of a matrix is bounded
by the product of the Euclidean norms of its rows. -/
theorem abs_det_le_prod_norm_toLp_two
    [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} :
    ‖A.det‖ ≤ ∏ i, ‖toLp 2 (A i)‖ := by
  obtain (h | h) := isEmpty_or_nonempty n
  · simp
  have hcard_pos : 0 < Fintype.card n := Fintype.card_pos
  let _ := Fintype.equivFin n |>.linearOrder
  -- These next few lines are because we are missing
  -- `Equiv.orderBot` and `Equiv.locallyFiniteOrderBot`
  have _ : OrderBot n :=
    { bot := (Fintype.equivFin n).invFun 0
      bot_le _ := show (Fintype.equivFin n) ((Fintype.equivFin n).invFun 0) ≤ _ by simp }
  have _ : LocallyFiniteOrderBot n := @LocallyFiniteOrder.toLocallyFiniteOrderBot _ _
    Fintype.toLocallyFiniteOrder _
  rw [norm_det_eq_prod_abs_inner_gramSchmidt_rows]
  gcongr
  let b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
    gramSchmidtOrthonormalBasis finrank_euclideanSpace (fun i => WithLp.toLp 2 (A i))
  simpa using norm_inner_le_norm (b i) (toLp 2 (A i))

/-- Hadamard's maximal determinant inequality for real matrices with entries bounded by one:
`|A.det| ≤ √((Fintype.card n : ℝ) ^ Fintype.card n)`. -/
theorem norm_det_le_sqrt_card_pow_card_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A.det‖ ≤ √((Fintype.card n : ℝ) ^ Fintype.card n) := by
  grw [abs_det_le_prod_norm_toLp_two, ← sq_le_sq₀ (by positivity) (by positivity)]
  simp only [Nat.cast_nonneg, pow_nonneg, Real.sq_sqrt, ← Finset.prod_pow]
  trans ∏ i : n, Fintype.card n
  · exact Finset.prod_le_prod (by intros; positivity) fun i _ ↦ euclidean_row_norm_sq_le_card hA i
  · simp

/-- Hadamard's maximal determinant inequality, squared form: `A.det ^ 2 ≤ n ^ n`. -/
theorem det_sq_le_card_pow_card_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A.det‖ ^ 2 ≤ (Fintype.card n : ℝ) ^ Fintype.card n := by
  grw [norm_det_le_sqrt_card_pow_card_of_abs_apply_le_one hA]
  simp

/-- The absolute value of the determinant of a real Hadamard matrix is the Hadamard bound. -/
theorem IsHadamard.abs_det_eq_sqrt_card_pow_card
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHadamard) :
    |A.det| = √((Fintype.card n : ℝ) ^ Fintype.card n) := by
  rw [← hA.det_mul_star_det]
  simp [Real.sqrt_mul_self_eq_abs]

/-- Equality in Hadamard's maximal determinant inequality characterizes real Hadamard matrices. -/
theorem isHadamard_of_abs_det_eq_sqrt_card_pow_card_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hbound : ∀ i j, |A i j| ≤ 1)
    (hdet : |A.det| = √((Fintype.card n : ℝ) ^ Fintype.card n)) :
    A.IsHadamard := by
  obtain (h | h) := isEmpty_or_nonempty n
  · simpa [isHadamard_iff] using Subsingleton.elim ..
  have hcard_pos : 0 < Fintype.card n := Fintype.card_pos
  let _ := Fintype.equivFin n |>.linearOrder
  -- These next few lines are because we are missing
  -- `Equiv.orderBot` and `Equiv.locallyFiniteOrderBot`
  have _ : OrderBot n :=
    { bot := (Fintype.equivFin n).invFun 0
      bot_le _ := show (Fintype.equivFin n) ((Fintype.equivFin n).invFun 0) ≤ _ by simp }
  have _ : LocallyFiniteOrderBot n := @LocallyFiniteOrder.toLocallyFiniteOrderBot _ _
    Fintype.toLocallyFiniteOrder _
  let v : n → EuclideanSpace ℝ n := fun i => WithLp.toLp 2 (A i)
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) :=
    gramSchmidtOrthonormalBasis finrank_euclideanSpace v
  have h_inner_le (i : n) : |⟪b i, v i⟫_ℝ| ≤ ‖v i‖ := by simpa using abs_real_inner_le_norm (b i) _
  /- By assumption and `abs_det_eq_prod_abs_inner_gramSchmidt_rows`, we have the following
    calculation:
    Fintype.card n ^ Fintype.card n = |A.det| ^ 2
    _ = ∏ i : n, |⟪b i, v i⟫_ℝ| ^ 2
    _ ≤ ∏ i : n, ‖v i‖ ^ 2
    _ ≤ ∏ i : n, Fintype.card n.
  Since the first and last terms are equal, all the terms in the products must be equal too.
  Thus `|⟪b i, v i⟫_ℝ| ^ 2 = ‖v i‖ = Fintype.card n` for all `i : n`-/
  have h_inner_eq_norm (i : n) : |⟪b i, v i⟫_ℝ| ^ 2 = Fintype.card n := by
    suffices ∏ i, |⟪b i, v i⟫_ℝ| ^ 2 = ∏ i : n, (Fintype.card n : ℝ) by
      rw [Finset.prod_eq_prod_iff_of_le_of_nonneg
        (fun _ _ ↦ by grw [h_inner_le, euclidean_row_norm_sq_le_card hbound])
        (by intros; positivity) (by positivity)] at this
      simpa [Finset.mem_univ, forall_const] using this i
    simp_rw [← Real.norm_eq_abs]
    rw [Finset.prod_pow, ← norm_det_eq_prod_abs_inner_gramSchmidt_rows]
    simp [hdet]
  have h_norm_sq (i : n) : ‖v i‖ ^ 2 = Fintype.card n :=
    (euclidean_row_norm_sq_le_card hbound i).antisymm <| by grw [← h_inner_eq_norm i, h_inner_le i]
  /- Since `∑ j, |A i j| ^ 2 = ‖v i‖ ^ 2 = Fintype.card n = ∑ j, 1` and the terms `|A i j| ≤ 1`,
  we conclude `|A i j| = 1` for all `i j : n`. Moreover, since `|⟪b i, v i⟫_ℝ| ^ 2 = ‖v i‖` for
  and `‖b i‖ = 1`, by the Cauchy--Schwarz inequality, the vector `v i` must be a scalar multiple
  of `b i`, hence the vectors `v i` and `v j` are orthogonal. Hence `A` is a Hadamard matrix. -/
  refine IsHadamard.of_entry_sq_of_pairwise_rows (fun i j => ?_) (fun i k hik => ?_)
  · exact (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (fun k _ => (sq_le_one_iff_abs_le_one (A i k)).2 (hbound i k))).mp
        (by simpa [v, EuclideanSpace.real_norm_sq_eq] using h_norm_sq i) j (Finset.mem_univ j)
  · have := gramSchmidtOrthonormalBasis_pairwise_inner_eq_zero_of_parallel (E := EuclideanSpace ℝ n)
      finrank_euclideanSpace v fun i ↦ by
        have := ((norm_inner_eq_norm_tfae ℝ (b i) (v i)).out 0 2).mp <| by
          rw [b.norm_eq_one, one_mul, ← sq_eq_sq₀ (by positivity) (by positivity)]
          grind [Real.norm_eq_abs]
        exact this.resolve_left (b.orthonormal.ne_zero i)
    simpa [v, PiLp.inner_apply, dotProduct, mul_comm] using this hik

/-- Under the entry bound `|A i j| ≤ 1`, equality in Hadamard's maximal determinant inequality
holds if and only if `A` is a real Hadamard matrix. -/
theorem abs_det_eq_sqrt_card_pow_card_iff_isHadamard_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hbound : ∀ i j, |A i j| ≤ 1) :
    |A.det| = √((Fintype.card n : ℝ) ^ Fintype.card n) ↔ A.IsHadamard :=
  ⟨isHadamard_of_abs_det_eq_sqrt_card_pow_card_of_abs_apply_le_one hbound,
    IsHadamard.abs_det_eq_sqrt_card_pow_card⟩

end Matrix
