/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Orthogonal

/-!
# Ordering star projections in star-ordered rings

## Main results

+ `IsStarProjection.sub_tfae`: equivalent conditions for `IsStarProjection (q - p)` in a star ring
  when `p` and `q` are star projections.
+ `IsStarProjection.le_tfae`: equivalent conditions for `p ≤ q` when `p` and `q` are star
  projections in a star-ordered ring with a proper star (e.g., a C⋆-algebra).
  This list subsumes the one appearing in `IsStarProjection.sub_tfae`.
-/

public section

open scoped StarRing

namespace IsStarProjection

variable {R : Type*} [NonUnitalRing R] [StarRing R]

section HasUniqueDiv

variable [HasUniqueDiv R] {p q : R}

/-- For star projections `p` and `q` in a star ring with no additive torsion, the following are
equivalent:
- `q * p = p`
- `p * q = p`
- `q - p` is a star projection
- `q - p` is an idempotent element
- `q * p * q = p`
- `p ⋆⟂ (q - p)` -/
lemma sub_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) :
    List.TFAE
      [q * p = p,
      p * q = p,
      IsStarProjection (q - p),
      IsIdempotentElem (q - p),
      q * p * q = p,
      p ⋆⟂ (q - p)] := by
  have h₁₂ (h : q * p = p) : p * q = p := by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 1 → 2 := h₁₂
  tfae_have 2 → 3 := hp.sub_of_mul_eq_left hq
  tfae_have 3 ↔ 4 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_have 4 → 1 := fun h ↦ (hp.isIdempotentElem.sub_iff hq.isIdempotentElem |>.mp h).2
  tfae_have 1 → 5 := fun h ↦ by rw [h, h₁₂ h]
  tfae_have 5 → 1 := fun h ↦ by rw [← h, ← mul_assoc, ← mul_assoc, hq.isIdempotentElem.eq]
  tfae_have 2 ↔ 6 := by
    rw [hp.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (hq.isSelfAdjoint.sub hp.isSelfAdjoint),
      mul_sub, hp.isIdempotentElem.eq, sub_eq_zero]
  tfae_finish

end HasUniqueDiv

section IsProperStar

variable [PartialOrder R] [StarOrderedRing R] [IsProperStar R] {p q : R}

/-- For star projections `p` and `q` in a star-ordered ring with a proper star (e.g., a
C⋆-algebra), the following are equivalent:
- `p ≤ q`
- `q * p = p`
- `p * q = p`
- `q - p` is a star projection
- `q - p` is idempotent
- `q * p * q = p`
- `p * q * p = p`
- `p ⋆⟂ (q - p)` -/
lemma le_tfae (hp : IsStarProjection p) (hq : IsStarProjection q) :
    List.TFAE
      [p ≤ q,
      q * p = p,
      p * q = p,
      IsStarProjection (q - p),
      IsIdempotentElem (q - p),
      q * p * q = p,
      p * q * p = p,
      p ⋆⟂ (q - p)] := by
  have h₂₃ (h : q * p = p) : p * q = p := by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 2 → 3 := h₂₃
  tfae_have 3 → 2 := fun h ↦ by
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $h)
  tfae_have 3 → 4 := hp.sub_of_mul_eq_left hq
  tfae_have 4 ↔ 5 := by simp [isStarProjection_iff, hq.isSelfAdjoint.sub hp.isSelfAdjoint]
  tfae_have 4 → 1 := fun h ↦ by simpa using h.nonneg
  tfae_have 1 → 7 := fun h ↦ by
    refine le_antisymm ?_ ?_
    · rw [← sub_nonneg]
      convert star_mul_self_nonneg (p - q * p) using 1
      simp [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, mul_sub, sub_mul, ← mul_assoc,
        hp.isIdempotentElem.eq, hq.isIdempotentElem.mul_mul_self]
    · simpa [hp.isIdempotentElem.mul_mul_self, hp.isIdempotentElem.eq] using
        hp.isSelfAdjoint.conjugate_le_conjugate h
  tfae_have 7 → 3 := fun h ↦ by
    rw [← sub_eq_zero, ← mul_star_self_eq_zero]
    simp [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, mul_sub, sub_mul, ← mul_assoc,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.mul_mul_self, h]
  tfae_have 2 → 6 := fun h ↦ by rw [h, h₂₃ h]
  tfae_have 6 → 2 := fun h ↦ by
    rw [← h, ← mul_assoc, ← mul_assoc, hq.isIdempotentElem.eq]
  tfae_have 3 ↔ 8 := by
    rw [hp.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (hq.isSelfAdjoint.sub hp.isSelfAdjoint),
      mul_sub, hp.isIdempotentElem.eq, sub_eq_zero]
  tfae_finish

lemma le_iff_mul_eq_right (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ q * p = p :=
  hp.le_tfae hq |>.out 1 2

lemma le_iff_mul_eq_left (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q = p :=
  hp.le_tfae hq |>.out 1 3

lemma le_iff_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ IsStarProjection (q - p) :=
  hp.le_tfae hq |>.out 1 4

lemma le_iff_idempotent_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ IsIdempotentElem (q - p) :=
  hp.le_tfae hq |>.out 1 5

lemma le_iff_mul_mul_eq (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ q * p * q = p :=
  hp.le_tfae hq |>.out 1 6

lemma le_iff_mul_mul_eq' (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q * p = p :=
  hp.le_tfae hq |>.out 1 7

lemma le_iff_isStarOrtho_sub (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p ⋆⟂ (q - p) :=
  hp.le_tfae hq |>.out 1 8

/-- If `p ≤ q` are star projections, then `q * p * q = p`. -/
alias ⟨mul_mul_eq_of_le, _⟩ := le_iff_mul_mul_eq

/-- If `p ≤ q` are star projections, then `p * q * p = p`. -/
alias ⟨mul_mul_eq_of_le', _⟩ := le_iff_mul_mul_eq'

lemma commute_of_le (hp : IsStarProjection p) (hq : IsStarProjection q) (h : p ≤ q) :
    Commute p q := by
  rw [commute_iff_eq, hp.le_iff_mul_eq_right hq |>.mp h, hp.le_iff_mul_eq_left hq |>.mp h]

end IsProperStar

end IsStarProjection
