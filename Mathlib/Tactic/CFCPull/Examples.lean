module

public import Mathlib
public import Mathlib.Tactic.CFCPull

/-!
# Examples for the `cfc_pull` tactic

This is the working test suite for `cfc_pull`. Each example states an identity between an
expression in a C⋆-algebra (or in any algebra with a continuous functional calculus) and the same
expression with `cfc`/`cfcₙ` pulled to the head, and proves it with `cfc_pull`.

`cfc_pull` produces the main goal (an equality of two `cfc` applications, which is closed by
`rfl` when the two functions agree) followed by the hypotheses of the lemmas it used. The
`+discharge` option additionally runs the standard auto-param tactics `cfc_tac`, `cfc_cont_tac`
and `cfc_zero_tac` on those side goals, which is what makes most of the examples below close
outright.

Examples that `cfc_pull` deliberately does *not* finish are marked as such; in every case what is
left over is either an honest side condition or an equality of functions that has to be settled
with `cfc_congr`.
-/

set_option maxHeartbeats 1000000

section GenericUnital

/- The user supplies the scalar ring `R` and the element `a`; the unital calculus is used because
the algebra has one. -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A]
  [StarRing A] [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
  [ContinuousMap.UniqueHom R A] {a : A} {f g : R → R}

example (ha : p a) :
    star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull +discharge R a

/-- Without `+discharge`, the continuity hypotheses are left to the user. -/
example (ha : p a) :
    star a * a = cfc (fun x : R ↦ star x * x) a := by
  cfc_pull R a <;> fun_prop

example (ha : p a) (hf : ContinuousOn f (spectrum R a)) (hg : ContinuousOn g (spectrum R a)) :
    star (cfc f a) + cfc g a + a = cfc (fun x ↦ star (f x) + g x + x) a := by
  cfc_pull +discharge R a

example (ha : p a) :
    a ^ 2 + 3 • a * cfc (id : R → R) a = cfc (fun x : R ↦ x ^ 2 + 3 • x * x) a := by
  cfc_pull +discharge R a

/- Composition: the calculus is applied to `a ^ 2` rather than to `a`, which `cfc_comp_pow`
resolves in one step. -/
example (ha : p a) (hf : ContinuousOn f ((· ^ 2) '' spectrum R a)) :
    cfc f (a ^ 2) = cfc (fun x ↦ f (x ^ 2)) a := by
  cfc_pull +discharge R a

/- A double composition: `cfc_comp_pow` peels off the power, and `cfc_comp'` the inner `cfc`. -/
example (ha : p a) (hf : Continuous f) (hg : ContinuousOn g (spectrum R a)) :
    cfc f ((cfc g a) ^ 2) = cfc (fun x ↦ f (g x ^ 2)) a := by
  cfc_pull +discharge R a

/- `cfc_pull` also works in `conv` mode, which is how one pulls at a specific position. -/
example (ha : p a) (b : A) :
    star a * a + b = cfc (fun x : R ↦ star x * x) a + b := by
  conv in star a * a => cfc_pull +discharge R a

end GenericUnital

section GenericNonUnital

/- Here the algebra is not unital, so `cfc_pull` falls back to `cfcₙ` without being told to. -/

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R]
  [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
  [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A]
  {a : A} {f g : R → R}

example (ha : p a) :
    star a * a = cfcₙ (fun x : R ↦ star x * x) a := by
  cfc_pull +discharge R a

example (ha : p a) (hf : ContinuousOn f (quasispectrum R a)) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum R a)) (hg0 : g 0 = 0) :
    star (cfcₙ f a) + cfcₙ g a + a = cfcₙ (fun x ↦ star (f x) + g x + x) a := by
  cfc_pull +discharge R a

example (ha : p a) :
    a * a + 3 • a * cfcₙ (id : R → R) a = cfcₙ (fun x : R ↦ x * x + 3 • x * x) a := by
  cfc_pull +discharge R a

/- Note that `cfc_pull` produces `f (x * x)`, not `f (x ^ 2)`: it follows the shape of the term
it is given, and there is no `cfcₙ_pow` to turn `a * a` into a square. -/
example (ha : p a) (hf : ContinuousOn f ((fun x : R ↦ x * x) '' quasispectrum R a))
    (hf0 : f 0 = 0) :
    cfcₙ f (a * a) = cfcₙ (fun x ↦ f (x * x)) a := by
  cfc_pull +discharge R a

example (ha : p a) (hf : Continuous f) (hf0 : f 0 = 0)
    (hg : ContinuousOn g (quasispectrum R a)) (hg0 : g 0 = 0) :
    cfcₙ f (cfcₙ g a * cfcₙ g a) = cfcₙ (fun x ↦ f (g x * g x)) a := by
  cfc_pull +discharge R a

end GenericNonUnital

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open Complex
open scoped NNReal

example (ha : IsStarNormal a) :
    NormedSpace.exp (I • a) = cfc (fun x ↦ Complex.exp (I • x)) a := by
  cfc_pull +discharge ℂ a

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp a = cfc Real.exp a := by
  cfc_pull +discharge ℝ a

example (ha : 0 ≤ a) :
    CFC.sqrt a = cfcₙ NNReal.sqrt a := by
  cfc_pull +discharge ℝ≥0 a

/- Over `ℝ`, `CFC.sqrt` is pulled with `CFC.sqrt_eq_real_sqrt` rather than by converting the
`ℝ≥0` calculus, which is why the function comes out as `Real.sqrt`. -/
example (ha : 0 ≤ a) :
    1 - CFC.sqrt a = cfc (fun x ↦ 1 - √x) a := by
  cfc_pull +discharge ℝ a

/- Here `f` is arbitrary, so its continuity is a genuine side goal. -/
example (ha : IsSelfAdjoint a) (f : ℝ≥0 → ℝ≥0) (hf0 : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 (CFC.sqrt (a ^ 2)))) :
    CFC.sqrt (CFC.sqrt (a ^ 2)) + cfcₙ f (CFC.sqrt (a ^ 2)) =
      cfcₙ (fun x ↦ NNReal.sqrt x + f x) (CFC.sqrt (a ^ 2)) := by
  cfc_pull +discharge

/- Pulling over `ℂ` a term whose natural home is the non-unital calculus over `ℝ`: `cfc_pull`
uses `CFC.posPart_def`, then `cfcₙ_eq_cfc`, then `cfc_real_eq_complex`. -/
example (ha : IsSelfAdjoint a) :
    a⁺ = cfc (fun z : ℂ ↦ (z.re⁺ : ℝ)) a := by
  cfc_pull +discharge ℂ a

/- `a⁺`/`a⁻`, keeping the non-unital `cfcₙ` head even in a unital algebra. -/
example (ha : IsSelfAdjoint a) :
    a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  cfc_pull +discharge -unital ℝ a

example :
    a⁺ * a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ * x⁻) a := by
  cfc_pull +discharge -unital ℝ a

/- Mixing the (non-unital) `a⁺` with the unital constant `1` forces a `cfc` head. -/
example (ha : IsSelfAdjoint a) :
    1 - a⁺ = cfc (fun x : ℝ ↦ 1 - x⁺) a := by
  cfc_pull +discharge ℝ a

/- `CFC.abs`, pulled over its own scalar ring `ℝ≥0` at the base point `star a * a`. -/
example (a : A) :
    CFC.abs a * CFC.abs a = cfcₙ (fun x : ℝ≥0 ↦ NNReal.sqrt x * NNReal.sqrt x) (star a * a) := by
  cfc_pull +discharge ℝ≥0 (star a * a)

/- `a ^ (x : ℝ)`, pulled over `ℝ≥0`. `CFC.rpow_def` is definitional, so there is nothing to
discharge here; the product below does need continuity, which `fun_prop` gets from `0 ≤ x`. -/
example (a : A) (x : ℝ) :
    a ^ x = cfc (fun t : ℝ≥0 ↦ t ^ x) a := by
  cfc_pull +discharge ℝ≥0 a

example (ha : 0 ≤ a) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a ^ x * a ^ y = cfc (fun t : ℝ≥0 ↦ t ^ x * t ^ y) a := by
  cfc_pull +discharge ℝ≥0 a

example (ha : 0 ≤ a) :
    CFC.sqrt a * CFC.sqrt a = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.sqrt t) a := by
  cfc_pull +discharge ℝ≥0 a

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp a * NormedSpace.exp a = cfc (fun x : ℝ ↦ Real.exp x * Real.exp x) a := by
  cfc_pull +discharge ℝ a

example (ha : IsStarNormal a) (z : ℂ) :
    NormedSpace.exp (z • a) = cfc (fun w : ℂ ↦ Complex.exp (z * w)) a := by
  cfc_pull +discharge ℂ a

/- `CFC.log` composed with `NormedSpace.exp`, pulled (not simplified away) into a single `cfc`. -/
example (ha : IsSelfAdjoint a) :
    CFC.log (NormedSpace.exp a) = cfc (fun x : ℝ ↦ Real.log (Real.exp x)) a := by
  cfc_pull +discharge ℝ a

example (ha : IsSelfAdjoint a) :
    NormedSpace.exp (-a) * NormedSpace.exp a = cfc (fun x : ℝ ↦ Real.exp (-x) * Real.exp x) a := by
  cfc_pull +discharge ℝ a

/- Inversion in `Aˣ`, using the unital `cfc`. -/
example (u : Aˣ) (ha : IsStarNormal (u : A)) :
    (↑u⁻¹ : A) = cfc (fun x : ℂ ↦ x⁻¹) (u : A) := by
  cfc_pull +discharge ℂ (u : A)

example (ha : IsStarNormal a) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) (hg : ContinuousOn g (spectrum ℂ a)) :
    cfc f a * cfc g a = cfc (fun z ↦ f z * g z) a := by
  cfc_pull +discharge ℂ a

end CStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a : A}

open Complex
open scoped NNReal

example :
    a⁺ - a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ - x⁻) a := by
  cfc_pull +discharge ℝ a

example :
    a⁺ * a⁻ = cfcₙ (fun x : ℝ ↦ x⁺ * x⁻) a := by
  cfc_pull +discharge ℝ a

example (a : A) :
    CFC.abs a = cfcₙ NNReal.sqrt (star a * a) := by
  cfc_pull +discharge ℝ≥0 (star a * a)

example (ha : 0 ≤ a) :
    CFC.sqrt a * CFC.sqrt a = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.sqrt t) a := by
  cfc_pull +discharge ℝ≥0 a

/- The element is `star a * a`, not `a` itself. -/
example (a : A) (f : ℝ≥0 → ℝ≥0) (hf0 : f 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 (star a * a))) :
    CFC.sqrt (star a * a) + cfcₙ f (star a * a) =
      cfcₙ (fun x ↦ NNReal.sqrt x + f x) (star a * a) := by
  cfc_pull +discharge ℝ≥0 (star a * a)

example (ha : IsStarNormal a) (f g : ℂ → ℂ) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : ContinuousOn f (quasispectrum ℂ a)) (hg : ContinuousOn g (quasispectrum ℂ a)) :
    cfcₙ f a * cfcₙ g a = cfcₙ (fun z ↦ f z * g z) a := by
  cfc_pull +discharge ℂ a

/- The predicate `IsSelfAdjoint a` is genuinely needed here and is left to the user. -/
example (ha : IsSelfAdjoint a) :
    (-a)⁺ = cfcₙ (fun x : ℝ ↦ (-x)⁺) a := by
  cfc_pull +discharge ℝ a

example (ha : 0 ≤ a) (y : ℝ≥0) (hy : y ≠ 0) :
    CFC.sqrt a * a ^ y = cfcₙ (fun t : ℝ≥0 ↦ NNReal.sqrt t * NNReal.nnrpow t y) a := by
  cfc_pull +discharge ℝ≥0 a

example (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hf : ContinuousOn f ((fun x : ℝ ↦ x⁺) '' quasispectrum ℝ a)) :
    cfcₙ f a⁺ = cfcₙ (fun x ↦ f (x⁺)) a := by
  cfc_pull +discharge ℝ a

example (ha : IsSelfAdjoint a) :
    (2 • a)⁺ = cfcₙ (fun x : ℝ ↦ (2 • x)⁺) a := by
  cfc_pull +discharge ℝ a

example (ha : IsStarNormal a) (z : ℂ) :
    z • star a = cfcₙ (fun w : ℂ ↦ z * star w) a := by
  cfc_pull +discharge ℂ a

end NonUnitalCStarAlgebra

section InTheWild

/- Goals of this shape have appeared in Mathlib. -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a : A}

open Complex
open scoped NNReal

example [Nontrivial A] (ha : IsSelfAdjoint a) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull +discharge ℂ a

/- `cfc_pull` converts from the non-unital calculus over `ℝ` to the unital one over `ℂ`. It does
not close the goal: it produces `fun x ↦ x + I * ↑√(1 - x.re ^ 2)`, whereas the statement asks
for `fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)`. Both are correct — `a` is selfadjoint, so the two
functions agree on `spectrum ℂ a` — and closing the gap is exactly the job of `cfc_congr`. -/
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • cfcₙ Real.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull +discharge ℂ a
  refine cfc_congr fun x hx ↦ ?_
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]

/- The same, but starting from `CFC.sqrt (1 - a ^ 2)`. `cfc_pull` uses `CFC.sqrt_eq_real_sqrt`,
whose hypothesis `0 ≤ 1 - a ^ 2` becomes a side goal. -/
example [Nontrivial A] (ha : IsSelfAdjoint a) (ha_norm : ‖a‖ ≤ 1) :
    a + I • CFC.sqrt (1 - a ^ 2) = cfc (fun x ↦ ↑x.re + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull +discharge ℂ a
  · refine cfc_congr fun x hx ↦ ?_
    rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx]
  · -- the side goal `0 ≤ 1 - a ^ 2` left by `CFC.sqrt_eq_real_sqrt`
    have key : (1 : A) - a ^ 2 = cfc (fun x : ℝ ↦ 1 - x ^ 2) a := by cfc_pull +discharge ℝ a
    rw [key]
    refine cfc_nonneg fun x hx ↦ ?_
    have hx' : |x| ≤ 1 := by
      simpa [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hx).trans ha_norm
    nlinarith [sq_abs x, abs_le.mp hx']

end InTheWild
