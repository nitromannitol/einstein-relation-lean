import EinsteinFull.External.DFGW.ResolventApproximationVariance

/-! # Quantitative Kipnis–Varadhan remainder bound

A resolvent parameter comparable to the inverse observation time bounds the normalized
mean-square remainder by the normalized resolvent norm and martingale approximation error.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A pointwise estimate for the normalized `L²` Kipnis–Varadhan remainder. -/
theorem norm_resolvent_remainder_le (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (n : ℕ) (t : ℝ≥0)
    (hlower : (1 / 2 : ℝ) ≤ (reciprocalShift n : ℝ) * t)
    (hupper : (reciprocalShift n : ℝ) * t ≤ 1) :
    (t : ℝ)⁻¹ * ‖timeIntegralLp hP f t - Z t‖ ^ 2 ≤
      36 * ((reciprocalShift n : ℝ) * ‖transitionResolvent hP (reciprocalShift n) f‖ ^ 2) +
      4 * ‖dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift n) f) 1 - Z 1‖ ^ 2 := by
  let a := reciprocalShift n
  let U := timeIntegralLp hP f t
  let D := dynkinIncrementLp hP (transitionResolventDomain hP a f) t
  let Q := transitionResolvent hP a f
  let E := ‖dynkinIncrementLp hP (transitionResolventDomain hP a f) 1 - Z 1‖ ^ 2
  have ha : 0 < (a : ℝ) := a.2
  have ht : 0 < (t : ℝ) := by
    by_contra h
    have hzero : (t : ℝ) = 0 := le_antisymm (le_of_not_gt h) t.coe_nonneg
    simp only [hzero, mul_zero] at hlower
    norm_num at hlower
  have hinv : (t : ℝ)⁻¹ ≤ 2 * (a : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ ht).2
    nlinarith
  have hbound := norm_timeIntegralLp_sub_resolvent_martingale_le hP f a t
  change ‖U - D‖ ≤ (2 + (a : ℝ) * t) * ‖Q‖ at hbound
  have hbound' : ‖U - D‖ ≤ 3 * ‖Q‖ := by nlinarith [norm_nonneg Q]
  have htriangle : ‖U - Z t‖ ≤ ‖U - D‖ + ‖D - Z t‖ := by
    calc
      ‖U - Z t‖ = ‖(U - D) + (D - Z t)‖ := by congr 1 <;> abel
      _ ≤ _ := norm_add_le _ _
  have hsq : ‖U - Z t‖ ^ 2 ≤ 18 * ‖Q‖ ^ 2 + 2 * ‖D - Z t‖ ^ 2 := by
    have h1 := norm_nonneg (U - Z t)
    have h2 := norm_nonneg (U - D)
    have h3 := norm_nonneg (D - Z t)
    have h4 := norm_nonneg Q
    nlinarith [sq_nonneg (3 * ‖Q‖ - ‖D - Z t‖)]
  have hvar := norm_resolvent_martingale_sub_limit_sq hP hcoord f Z hZ n t
  change ‖D - Z t‖ ^ 2 = (t : ℝ) * E at hvar
  have hscaled := mul_le_mul_of_nonneg_left hsq ha.le
  rw [hvar] at hscaled
  have hscale : (a : ℝ) * ‖U - Z t‖ ^ 2 ≤ 18 * ((a : ℝ) * ‖Q‖ ^ 2) + 2 * E := by
    have hE0 : 0 ≤ E := sq_nonneg _
    have hprod : ((a : ℝ) * (t : ℝ)) * E ≤ E := by nlinarith
    calc
      _ ≤ (a : ℝ) * (18 * ‖Q‖ ^ 2 + 2 * ((t : ℝ) * E)) := hscaled
      _ = 18 * ((a : ℝ) * ‖Q‖ ^ 2) + 2 * (((a : ℝ) * t) * E) := by ring
      _ ≤ _ := by linarith
  have hratio := mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖U - Z t‖)
  change (t : ℝ)⁻¹ * ‖U - Z t‖ ^ 2 ≤ 36 * ((a : ℝ) * ‖Q‖ ^ 2) + 4 * E
  nlinarith

end EinsteinFull.External.DFGW
