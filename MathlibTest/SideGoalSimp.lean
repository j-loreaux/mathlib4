module

import Mathlib.Tactic.SideGoalSimp
import Mathlib.Algebra.GroupWithZero.NeZero

set_option linter.unusedVariables false

variable {G : Type*} [GroupWithZero G]

/-- Hypotheses proved by assumption do not become side goals. -/
example (a : G) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  simp_side only [mul_inv_cancel₀]

example (a b : G) (h : a ≠ 0 ∧ b ≠ 0) : a * a⁻¹ * (b * b⁻¹) = 1 := by
  simp_side only [mul_inv_cancel₀, mul_one] =>
    case h => guard_target = a ≠ 0; exact h.1
    case h => guard_target = b ≠ 0; exact h.2

/-- The side goal `a ≠ 0` is created only once. -/
example (a : G) (ha : 0 ≠ a) : a * a⁻¹ = a⁻¹ * a := by
  simp_side only [mul_inv_cancel₀, inv_mul_cancel₀] =>
    guard_target = a ≠ 0
    exact Ne.symm ha

/-- Under a binder, the side goal is quantified over the bound variable. -/
example (f : ℕ → ℕ) (hf : ∀ x (_hpos : 0 < x), f x = x) :
    (fun x ↦ f (x + 1)) = (· + 1) := by
  simp_side only [hf] =>
    guard_target = ∀ x : ℕ, 0 < x + 1
    lia

/-- Only `hpos` becomes a side goal: `hle` is discharged by assumption. -/
example (f : ℕ → ℕ) (hf : ∀ x (hpos : 0 < x) (hle : x ≤ 5), f x = x) (h : 3 ≤ 5) :
    f 3 = 3 := by
  simp_side only [hf with hpos] =>
    guard_target = 0 < 3
    decide

/-- error: simplification with side goals made no progress -/
#guard_msgs in
example (f : ℕ → ℕ) (hf : ∀ x (hpos : 0 < x) (hle : x ≤ 5), f x = x) : f 3 = 3 := by
  simp_side only [hf with hpos]

/--
error: unsolved goals
case mul_inv_cancel₀.h
G : Type u_1
inst✝ : GroupWithZero G
a : G
⊢ a ≠ 0
-/
#guard_msgs in
example (a : G) : a * a⁻¹ = 1 := by
  simp_side only [mul_inv_cancel₀] => skip

/--
error: unsolved side goals, prove them with `simp_side ... => tac`
case mul_inv_cancel₀.h
G : Type u_1
inst✝ : GroupWithZero G
a : G
⊢ a ≠ 0
-/
#guard_msgs in
example (a : G) : a * a⁻¹ = 1 := by
  simp_side only [mul_inv_cancel₀]

section attr

theorem my_mul_inv_cancel (a : G) (ha : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ ha

attribute [local side_goal_simp] my_mul_inv_cancel

example (a : G) (ha : 0 ≠ a) : a * a⁻¹ = 1 := by
  simp_side => exact Ne.symm ha

/-- error: `inv_mul_cancel₀` has no hypothesis named `hb` -/
#guard_msgs in
attribute [local side_goal_simp hb] inv_mul_cancel₀

/-- error: the hypothesis `a` cannot become a side goal, it is not a proposition
  G -/
#guard_msgs in
attribute [local side_goal_simp a] my_mul_inv_cancel

end attr

section trace

/--
info: Try this:
  [apply] simp_side only [mul_inv_cancel₀]
-/
#guard_msgs in
example (a : G) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  simp_side? only [mul_inv_cancel₀, inv_mul_cancel₀]

/--
info: Try this:
  [apply] simp_side only [hf with hpos] => decide
-/
#guard_msgs in
example (f : ℕ → ℕ) (hf : ∀ x (hpos : 0 < x) (hle : x ≤ 5), f x = x) (h : 3 ≤ 5) :
    f 3 = 3 := by
  simp_side? only [hf with hpos, mul_inv_cancel₀] => decide

end trace
