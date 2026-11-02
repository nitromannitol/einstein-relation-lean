import EinsteinFull.Calculus.ComplexTransposeContinuitySupport
import EinsteinFull.Calculus.ComplexHorizontalMeanSupport
import EinsteinFull.Calculus.ComplexLpSupport

/-!
# Constants, means and centering for the actual stationary families

The full weak generator annihilates actual constant L2 classes. Right orbit
derivatives then give constant preservation, hence transpose mean preservation
and the centered forward/transpose identities needed for decay estimates.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Every actual constant L2 class belongs to the full forced generator kernel. -/
theorem isComplexGeneratorPair_const {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ c : ℂ) :
    letI := reducedLaw_probability Q
    IsComplexGeneratorPair Q i ζ (Lp.const 2 (reducedLaw Q) c) 0 := by
  letI := reducedLaw_probability Q
  refine ⟨fun _ => 0,
    hasComplexHorizontalGradient_const (reducedLaw Q) (reducedLaw_stationary Q) c, ?_⟩
  intro v V _
  have hz := Lp.coeFn_zero ℂ 2 (reducedLaw Q)
  have hl : (∫ ω, (0 : Lp ℂ 2 (reducedLaw Q)) ω * v ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with ω hω
    simp only [hω, Pi.zero_apply, zero_mul]
  have ha : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω * V j ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]
  have hb : (∫ ω, (∑ j, (ω.1 0 j i : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω) * v ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]
  simp only [hl, ha, hb, mul_zero, add_zero]

/-- Every vector in the full actual generator kernel is fixed by any complete frozen family. -/
theorem IsComplexEnvironmentSemigroup.map_kernel {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f : Lp ℂ 2 (reducedLaw Q)} (hf : IsComplexGeneratorPair Q i ζ f 0) (t : ℝ≥0) :
    P t f = f := by
  have hc := (hP.2.2.1 f).comp continuous_real_toNNReal
  have he := constant_of_has_deriv_right_zero (a := 0) (b := (t : ℝ)) hc.continuousOn
    (fun s hs => by simpa only [map_zero, Function.comp_def] using! hP.hasDerivWithinAt_orbit hf s hs.1)
    (t : ℝ) ⟨t.property, le_rfl⟩
  simpa only [Function.comp_apply, Real.toNNReal_coe, Real.toNNReal_zero, hP.1,
    ContinuousLinearMap.id_apply] using he

/-- Every complete stationary complex semigroup preserves actual constant L2 classes. -/
theorem IsComplexEnvironmentSemigroup.map_const {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) (c : ℂ) :
    letI := reducedLaw_probability Q
    P t (Lp.const 2 (reducedLaw Q) c) = Lp.const 2 (reducedLaw Q) c :=
  hP.map_kernel (isComplexGeneratorPair_const Q i ζ c) t

/-- The actual bilinear transpose preserves the reduced-law mean, at every complex force. -/
theorem IsComplexTransposeSemigroup.integral_eq {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, R t f ω ∂reducedLaw Q) = ∫ ω, f ω ∂reducedLaw Q := by
  letI := reducedLaw_probability Q
  have hc (g : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, Lp.const 2 (reducedLaw Q) (1 : ℂ) ω * g ω ∂reducedLaw Q) =
        ∫ ω, g ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, one_mul]
  have h := hR t (Lp.const 2 (reducedLaw Q) 1) f
  rw [hP.map_const, hc, hc] at h
  exact h.symm

/-- Subtracting an actual constant class does not change the centered observation. -/
theorem centeredComplexLp_sub_const {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q)) (c : ℂ) :
    letI := reducedLaw_probability Q
    centeredComplexLp Q (f - Lp.const 2 (reducedLaw Q) c) = centeredComplexLp Q f := by
  letI := reducedLaw_probability Q
  have hc : (∫ ω, Lp.const 2 (reducedLaw Q) c ω ∂reducedLaw Q) = c := by
    rw [integral_congr_ae (Lp.coeFn_const 2 (reducedLaw Q) c)]
    simp only [Function.const_apply, integral_const, probReal_univ, one_smul]
  have hi : Integrable (fun ω => Lp.const 2 (reducedLaw Q) c ω) (reducedLaw Q) :=
    integrable_complexLp Q _
  have hm : (∫ ω, (f-Lp.const 2 (reducedLaw Q) c) ω ∂reducedLaw Q) =
      (∫ ω, f ω ∂reducedLaw Q) - c := by
    rw [integral_congr_ae (Lp.coeFn_sub f (Lp.const 2 (reducedLaw Q) c))]
    change (∫ ω, f ω - Lp.const 2 (reducedLaw Q) c ω ∂reducedLaw Q) = _
    rw [integral_sub (integrable_complexLp Q f) hi, hc]
  change (f-Lp.const 2 (reducedLaw Q) c) -
    Lp.const 2 (reducedLaw Q) (∫ ω, (f-Lp.const 2 (reducedLaw Q) c) ω ∂reducedLaw Q) = _
  rw [hm, map_sub]
  change _ = f - Lp.const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q)
  abel

/-- Centering before the forward evolution does not affect its centered output. -/
theorem IsComplexEnvironmentSemigroup.centered_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (P t (centeredComplexLp Q f)) = centeredComplexLp Q (P t f) := by
  letI := reducedLaw_probability Q
  have he : P t (centeredComplexLp Q f) =
      P t f - Lp.const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q) := by
    change P t (f-Lp.const 2 (reducedLaw Q) _) = _
    rw [map_sub, hP.map_const]
  rw [he, centeredComplexLp_sub_const]

/-- The transpose sends centered data to centered data for every complex force. -/
theorem IsComplexTransposeSemigroup.centered_apply_centered {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (R t (centeredComplexLp Q f)) = R t (centeredComplexLp Q f) := by
  letI := reducedLaw_probability Q
  have hm := hR.integral_eq hP t (centeredComplexLp Q f)
  rw [integral_centeredComplexLp] at hm
  change R t (centeredComplexLp Q f) - Lp.const 2 (reducedLaw Q) _ = _
  rw [hm, map_zero, sub_zero]

end EinsteinFull
