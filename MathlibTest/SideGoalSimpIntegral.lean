module

import Mathlib.Tactic.SideGoalSimp
import Mathlib.Tactic.GoalToHave
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

open MeasureTheory

attribute [local side_goal_simp] integral_add integral_sub integral_neg integral_smul
  integral_const_mul integral_mul_const integral_div integral_finsetSum integral_zero

attribute [local side_goal_simp] intervalIntegral.integral_add intervalIntegral.integral_sub
  intervalIntegral.integral_neg intervalIntegral.integral_smul intervalIntegral.integral_const_mul
  intervalIntegral.integral_mul_const intervalIntegral.integral_div
  intervalIntegral.integral_finsetSum intervalIntegral.integral_zero

/- probably this is not the lemma we actually want, but it was necessary for now to
make `fun_prop` work on a certain goal. -/
theorem Continuous.intervalIntegrable_comp {E F : Type*} [NormedAddCommGroup E]
    [TopologicalSpace F] {f : F → E} {g : ℝ → F} (hf : Continuous f) (hg : Continuous g)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {a b : ℝ} :
    IntervalIntegrable (fun x ↦ f (g x)) μ a b :=
  (hf.comp hg).intervalIntegrable a b

attribute [local fun_prop] IntervalIntegrable Continuous.intervalIntegrable
  Continuous.intervalIntegrable_comp intervalIntegral.intervalIntegrable_id intervalIntegrable_const
  IntervalIntegrable.add IntervalIntegrable.sub IntervalIntegrable.const_mul
  IntervalIntegrable.mul_const IntervalIntegrable.div_const

section Bochner

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → ℝ} {u v : α → E}

example (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x + 2 * g x) ∂μ = ∫ x, f x ∂μ + 2 * ∫ x, g x ∂μ := by
  simp_side => fun_prop

example (hu : Integrable u μ) (hv : Integrable v μ) (c : ℝ) :
    ∫ x, (c • u x - -v x) ∂μ = c • ∫ x, u x ∂μ - -∫ x, v x ∂μ := by
  simp_side => all_goals fun_prop

/-- Side goal dedupilication. -/
example (h : Integrable f μ ∧ Integrable g μ) :
    ∫ x, (f x + g x) ∂μ + ∫ x, (f x - g x) ∂μ = 2 * ∫ x, f x ∂μ := by
  simp_side =>
    case integral_add.hf => exact h.1
    case integral_add.hg => exact h.2
  ring

example {ι : Type*} (s : Finset ι) (F : ι → α → ℝ) (hF : ∀ i ∈ s, Integrable (F i) μ) :
    ∫ x, ∑ i ∈ s, 3 * F i x ∂μ = 3 * ∑ i ∈ s, ∫ x, F i x ∂μ := by
  simp_side [Finset.mul_sum] =>
    -- ⊢ ∀ i ∈ s, Integrable ((fun i a => 3 * F i a) i) μ
    fun_prop

end Bochner

section Interval

open intervalIntegral

example : ∫ x in (0 : ℝ)..1, (Real.sin x + 3 * x ^ 2) =
    (∫ x in (0 : ℝ)..1, Real.sin x) + 3 * ∫ x in (0 : ℝ)..1, x ^ 2 := by
  simp_side => all_goals fun_prop

/-- The side goals are left to the user. -/
example (a b : ℝ) : ∫ x in a..b, (Real.cos x - x) = (∫ x in a..b, Real.cos x) - ∫ x in a..b, x := by
  simp_side =>
    case integral_sub.hf =>
      guard_target = IntervalIntegrable (fun x ↦ Real.cos x) MeasureTheory.volume a b
      fun_prop
    case integral_sub.hg =>
      guard_target = IntervalIntegrable (fun x ↦ x) MeasureTheory.volume a b
      fun_prop

/-- rewriting under integrals, easily discharging side goals. -/
example : (∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (t * x ^ 2 + Real.exp x)) =
    (∫ t in (0 : ℝ)..1, t * (∫ x in (0 : ℝ)..1, x ^ 2) + ∫ x in (0 : ℝ)..1, Real.exp x) := by
  simp_side => all_goals fun_prop

/-- In general, rewriting under binders. -/
example : (fun t ↦ ∫ x in (0 : ℝ)..1, (t * x ^ 2 + Real.exp x)) =
    fun t ↦ t * (∫ x in (0 : ℝ)..1, x ^ 2) + ∫ x in (0 : ℝ)..1, Real.exp x := by
  simp_side => all_goals fun_prop

/-- We needed `Continuous.intervalIntegrable_comp` for this because `fun_prop` can't
use the transition lemma first? -/
example (f : ℝ → ℝ) (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    ∫ x in (0 : ℝ)..1, (Real.sin (x ^ 2) - 2 * f x / 3) =
      (∫ x in (0 : ℝ)..1, Real.sin (x ^ 2)) - (2 * ∫ x in (0 : ℝ)..1, f x) / 3 := by
  simp_side => all_goals fun_prop

/-- The matcher of `Sym.simp` eta-reduces `fun x ↦ 2 * x` to `HMul.hMul 2`, which the pattern
`fun x ↦ ?r * ?f x` of `integral_const_mul` does not match.

Maybe this should be considered a bug? -/
example : ∫ x in (0 : ℝ)..1, 2 * x = 2 * ∫ x in (0 : ℝ)..1, x := by
  fail_if_success simp_side
  exact intervalIntegral.integral_const_mul 2 _

end Interval

section InTheWild

/- A few extant examples from Mathlib. -/

section Covariance

open ProbabilityTheory

attribute [local side_goal_simp] integral_const

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

/-- `ProbabilityTheory.covariance_eq_sub`, with its proof in Mathlib. -/
example (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y] := by
  simp_rw [covariance, sub_mul, mul_sub]
  repeat rw [integral_sub]
  · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
      one_smul]
    simp
  · exact hY.const_mul _ |>.integrable (by simp)
  · exact integrable_const _
  · exact hX.integrable_mul hY
  · exact hX.mul_const _ |>.integrable (by simp)
  · exact (hX.integrable_mul hY).sub (hX.mul_const _ |>.integrable (by simp))
  · exact (hY.const_mul _ |>.integrable (by simp)).sub (integrable_const _)

/-- `ProbabilityTheory.covariance_eq_sub`, with `simp_side`. -/
example (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y] := by
  have : Integrable (fun ω ↦ X ω * Y ω) μ := hX.integrable_mul hY
  have := hX.integrable one_le_two
  have := hY.integrable one_le_two
  simp_side [covariance.eq_def, sub_mul, mul_sub] => all_goals fun_prop
  simp

/-- `ProbabilityTheory.variance_le_sub_mul_sub`, with its proof in Mathlib. -/
example {a b : ℝ} {X : Ω → ℝ} (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ (b - μ[X]) * (μ[X] - a) := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h => h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω ↦ -X ω ^ 2) μ :=
    (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω ↦ (a + b) * X ω) μ :=
    ((integrable_const (max |a| |b|)).mono' hX.aestronglyMeasurable
      (by filter_upwards [ha, hb] with ω using abs_le_max_abs_abs)).const_mul (a + b)
  have h0 : 0 ≤ -μ[X ^ 2] + (a + b) * μ[X] - a * b :=
    calc
      _ ≤ ∫ ω, (b - X ω) * (X ω - a) ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [ha, hb] with ω ha' hb'
        exact mul_nonneg (by linarith : 0 ≤ b - X ω) (by linarith : 0 ≤ X ω - a)
      _ = ∫ ω, -X ω ^ 2 + (a + b) * X ω - a * b ∂μ :=
        integral_congr_ae <| ae_of_all μ fun ω ↦ by ring
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - ∫ _, a * b ∂μ :=
        integral_sub (by fun_prop) (integrable_const (a * b))
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - a * b := by simp
      _ = - μ[X ^ 2] + (a + b) * μ[X] - a * b := by
        simp [← integral_neg, ← integral_const_mul, integral_add hX_int₂ hX_int₁]
  calc
    _ ≤ (a + b) * μ[X] - a * b - μ[X] ^ 2 := by
      rw [variance_eq_sub (memLp_of_bounded h hX.aestronglyMeasurable 2)]
      linarith
    _ = (b - μ[X]) * (μ[X] - a) := by ring

/-- `ProbabilityTheory.variance_le_sub_mul_sub`, with `simp_side`. -/
example {a b : ℝ} {X : Ω → ℝ} (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ (b - μ[X]) * (μ[X] - a) := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h => h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω ↦ -X ω ^ 2) μ :=
    (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω ↦ (a + b) * X ω) μ :=
    ((integrable_const (max |a| |b|)).mono' hX.aestronglyMeasurable
      (by filter_upwards [ha, hb] with ω using abs_le_max_abs_abs)).const_mul (a + b)
  have h0 : 0 ≤ -μ[X ^ 2] + (a + b) * μ[X] - a * b :=
    calc
      _ ≤ ∫ ω, (b - X ω) * (X ω - a) ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [ha, hb] with ω ha' hb'
        exact mul_nonneg (by linarith : 0 ≤ b - X ω) (by linarith : 0 ≤ X ω - a)
      _ = ∫ ω, -X ω ^ 2 + (a + b) * X ω - a * b ∂μ :=
        integral_congr_ae <| ae_of_all μ fun ω ↦ by ring
      _ = -μ[X ^ 2] + (a + b) * μ[X] - a * b := by
        simp_side => all_goals fun_prop
        simp
  calc
    _ ≤ (a + b) * μ[X] - a * b - μ[X] ^ 2 := by
      rw [variance_eq_sub (memLp_of_bounded h hX.aestronglyMeasurable 2)]
      linarith
    _ = (b - μ[X]) * (μ[X] - a) := by ring

end Covariance

section SinPow

open Real
open scoped Interval

/-- `integral_sin_pow_aux`, with its proof in Mathlib. -/
example {a b : ℝ} (n : ℕ) :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b + (↑n + 1) * ∫ x in a..b, sin x ^ n) -
        (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : ℕ) * cos x * sin x ^ n) x :=
    fun x _ => by simpa only [mul_right_comm] using! (hasDerivAt_sin x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (-cos) (sin x) x := fun x _ => by
    simpa only [neg_neg] using! (hasDerivAt_cos x).neg
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  · calc
      (∫ x in a..b, sin x ^ (n + 2)) = ∫ x in a..b, sin x ^ (n + 1) * sin x := by
        simp only [_root_.pow_succ]
      _ = C + (↑n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n := by simp [H, h, sq]; ring
      _ = C + (↑n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) := by
        simp [cos_sq', sub_mul, ← pow_add, add_comm]
      _ = (C + (↑n + 1) * ∫ x in a..b, sin x ^ n) - (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
        rw [intervalIntegral.integral_sub, mul_sub, add_sub_assoc] <;>
          apply Continuous.intervalIntegrable <;> fun_prop
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- `integral_sin_pow_aux`, with `simp_side`. -/
example {a b : ℝ} (n : ℕ) :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b + (↑n + 1) * ∫ x in a..b, sin x ^ n) -
        (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : ℕ) * cos x * sin x ^ n) x :=
    fun x _ => by simpa only [mul_right_comm] using! (hasDerivAt_sin x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (-cos) (sin x) x := fun x _ => by
    simpa only [neg_neg] using! (hasDerivAt_cos x).neg
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  · calc
      (∫ x in a..b, sin x ^ (n + 2)) = ∫ x in a..b, sin x ^ (n + 1) * sin x := by
        simp only [_root_.pow_succ]
      _ = C + (↑n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n := by simp [H, h, sq]; ring
      _ = C + (↑n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) := by
        simp [cos_sq', sub_mul, ← pow_add, add_comm]
      _ = (C + (↑n + 1) * ∫ x in a..b, sin x ^ n) - (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
        simp_side => all_goals fun_prop
        ring
  all_goals fun_prop

end SinPow

end InTheWild
