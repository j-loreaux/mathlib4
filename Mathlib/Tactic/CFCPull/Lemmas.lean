/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Tactic.CFCPull.Frontend
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# The `@[cfc_pull]` lemma set

This file tags the Mathlib lemmas that the `cfc_pull` tactic uses, and supplies the handful of
definitional lemmas (`CFC.sqrt_def`, `CFC.abs_def`, `CFC.log_def`) that were missing.

Collecting the tags here rather than at the declaration sites keeps the tactic and its lemma set
in one place while `cfc_pull` is being developed. They should eventually move next to the lemmas
themselves, which is why `Mathlib/Tactic/CFCPull/Attr.lean` deliberately does not depend on the
analysis library.

`#cfc_pull_lemmas` prints the resulting database.
-/

@[expose] public section

open scoped NNReal

/-! ### Missing definitional lemmas -/

namespace CFC

section sqrt

variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

lemma sqrt_def (a : A) : sqrt a = cfcₙ NNReal.sqrt a := rfl

lemma abs_def (a : A) : abs a = cfcₙ NNReal.sqrt (star a * a) := rfl

end sqrt

section log

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma log_def (a : A) : log a = cfc Real.log a := rfl

end log

end CFC

/-! ### The identity

These are the base case of the recursion: they are what makes the element `a` itself pull to
`cfc (fun x ↦ x) a`. -/

attribute [cfc_pull] cfc_id' cfcₙ_id'

/-! ### Algebraic operations

Both the general lemmas and their `_id` specialisations are tagged. The specialisations match
strictly less often but have fewer hypotheses, and `cfc_pull` prefers them because they have
fewer holes. -/

attribute [cfc_pull]
  cfc_add cfc_sub cfc_neg cfc_mul cfc_pow cfc_smul cfc_star
  cfc_neg_id cfc_pow_id cfc_smul_id cfc_star_id
  cfc_const cfc_const_one cfc_const_zero
  cfc_const_add cfc_add_const

attribute [cfc_pull]
  cfcₙ_add cfcₙ_sub cfcₙ_neg cfcₙ_mul cfcₙ_smul cfcₙ_star
  cfcₙ_neg_id cfcₙ_smul_id cfcₙ_star_id
  cfcₙ_const_zero

/- `cfc_const_mul` and friends produce `fun x ↦ r * f x` rather than `fun x ↦ r • f x`, which is
what one wants whenever the scalar already lives in the ring the calculus is taken over; they are
given a higher priority so that they are tried before `cfc_smul`. -/
attribute [cfc_pull 1100] cfc_const_mul cfc_const_mul_id cfcₙ_const_mul cfcₙ_const_mul_id

/-! ### Changing the scalar ring and the unitality -/

attribute [cfc_pull]
  cfc_nnreal_eq_real cfcₙ_nnreal_eq_real
  cfc_real_eq_complex cfcₙ_real_eq_complex
  cfcₙ_eq_cfc

/-! ### Composition

`cfc_comp'` is the fallback used whenever the calculus is applied to something other than the
element being pulled towards; the other lemmas are shortcuts that avoid a continuity side goal
for the inner function. -/

attribute [cfc_pull] cfc_comp' cfc_comp_pow cfc_comp_smul cfc_comp_star cfc_comp_neg
attribute [cfc_pull 1100] cfc_comp_const_mul

attribute [cfc_pull] cfcₙ_comp' cfcₙ_comp_smul cfcₙ_comp_star cfcₙ_comp_neg
attribute [cfc_pull 1100] cfcₙ_comp_const_mul

/-! ### Specific functions defined via the calculus -/

attribute [cfc_pull]
  CFC.posPart_def CFC.negPart_def
  CFC.sqrt_def CFC.sqrt_eq_cfc CFC.abs_def
  CFC.nnrpow_def CFC.rpow_def
  CFC.log_def
  CFC.exp_eq_normedSpace_exp

/- The `ℝ`- and `ℂ`-specific exponential lemmas produce `Real.exp` and `Complex.exp` rather than
`NormedSpace.exp`, so they are preferred at those rings. -/
attribute [cfc_pull 1100] CFC.real_exp_eq_normedSpace_exp CFC.complex_exp_eq_normedSpace_exp
