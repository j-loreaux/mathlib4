module

import Mathlib.Tactic.GoalToHave
import Mathlib.Algebra.Group.Basic

/-!
# Tests for the "Turn goal into `have`" code actions

The code actions themselves are not tested here (they are only visible to an editor); these
examples exhibit the goal shapes they are meant to handle. The comments show the edit produced by
"Turn all goals into `have`s" with the cursor on the tactic marked `-- ←`.
-/

/-- A named goal (`left`), and multiple goals.
`have left : p := by sorry` / `have right : q := by sorry` -/
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor -- ←
  · exact hp
  · exact hq

/-- Goals tagged automatically by `refine`:
`have refine_1 : p := by sorry` / `have refine_2 : q := by sorry` -/
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩ -- ←
  · exact hp
  · exact hq

/-- An anonymous goal: `have : p := by sorry` -/
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, hq⟩ -- ←
  exact hp

/-- Hierarchical names: `have bar : p := by sorry` / `have baz : q := by sorry` -/
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?foo.bar, ?baz⟩ -- ←
  case bar => exact hp
  case baz => exact hq

/-- A clash with a hypothesis in context: `have h_1 : p := by sorry` -/
example (p q : Prop) (h : q) (hp : p) : p ∧ q := by
  refine ⟨?foo.h, h⟩ -- ←
  exact hp

/-- A goal mentioning an inaccessible hypothesis: `have : ∀ (n : ℕ), n = n := by sorry` -/
example : ∀ n : ℕ, n + 0 = n := by
  intro
  refine Eq.trans (Nat.add_zero _) ?_ -- ←
  rfl

/-- A goal mentioning a hypothesis introduced by the tactic itself:
`have : ∀ (n : ℕ), n + 0 = n := by sorry` -/
example : ∀ n : ℕ, n + 0 = n := by
  intro n -- ←
  rfl

/-- A long goal, printed on several lines. -/
example (a b c d e f g : ℕ) :
    a + b + c + d + e + f + g + a + b + c + d + e + f + g + a + b + c + d + e + f + g + a + b =
      a + b + c + d + e + f + g + a + b + c + d + e + f + g + a + b + c + d + e + f + g + a + b ∧
    True := by
  constructor -- ←
  · rfl
  · trivial

/-- A goal with an instance in context, and an inline tactic after `·`:
`have : a * (a⁻¹ * a) = a := by sorry` -/
example {G : Type*} [Group G] (a : G) (h : a = 1) : a * a⁻¹ * a = a ∧ a = 1 := by
  constructor
  · rw [mul_assoc] -- ←
    simp
  · exact h

/-- A goal containing a proof, printed with `pp.proofs` instead of `⋯`:
`have left : ⟨0, hn⟩ = x := by sorry` -/
example (n : ℕ) (hn : 0 < n) (x : Fin n) (h : x = ⟨0, hn⟩) : (⟨0, hn⟩ : Fin n) = x ∧ True := by
  constructor -- ←
  · exact h.symm
  · trivial
