import EinsteinFull.External.DFGW.ResolventApproximationVariance

/-! # Sublinear resolvent remainder at integer times

Along increasing integer times, the difference between the integrated observable and its
limiting resolvent martingale has variance negligible compared with elapsed time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The resolvent remainder, divided by the integer time scale, has vanishing squared `L²` norm. -/
theorem tendsto_resolvent_remainder_integer (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t))) :
    Tendsto (fun n : ℕ => (reciprocalShift n : ℝ) *
      ‖timeIntegralLp hP f ((n : ℝ≥0) + 1) - Z ((n : ℝ≥0) + 1)‖ ^ 2) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun n => (reciprocalShift n : ℝ) *
    ‖transitionResolvent hP (reciprocalShift n) f‖ ^ 2
  let E : ℕ → ℝ := fun n => ‖dynkinIncrementLp hP
    (transitionResolventDomain hP (reciprocalShift n) f) 1 - Z 1‖ ^ 2
  have hR : Tendsto R atTop (𝓝 0) := tendsto_reciprocalShift_mul_resolvent_norm_sq hP f hint
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := ((hZ 1).sub_const (Z 1)).norm.pow 2
    simpa [E] using h
  have hupper : Tendsto (fun n : ℕ => 18 * R n + 2 * E n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hR.const_mul 18).add (hE.const_mul 2)
  apply squeeze_zero (g := fun n : ℕ => 18 * R n + 2 * E n)
  · intro n
    exact mul_nonneg (reciprocalShift n).2.le (sq_nonneg _)
  · intro n
    let t : ℝ≥0 := (n : ℝ≥0) + 1
    let a := reciprocalShift n
    let U := timeIntegralLp hP f t
    let D := dynkinIncrementLp hP (transitionResolventDomain hP a f) t
    let Q := transitionResolvent hP a f
    have ha : 0 < (a : ℝ) := a.2
    have hat : (a : ℝ) * (t : ℝ) = 1 := by
      dsimp only [a, t, reciprocalShift]
      simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
      field_simp
    have hbound := norm_timeIntegralLp_sub_resolvent_martingale_le hP f a t
    change ‖U - D‖ ≤ (2 + (a : ℝ) * t) * ‖Q‖ at hbound
    rw [hat] at hbound
    have htriangle : ‖U - Z t‖ ≤ ‖U - D‖ + ‖D - Z t‖ := by
      calc
        ‖U - Z t‖ = ‖(U - D) + (D - Z t)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hsq : ‖U - Z t‖ ^ 2 ≤ 18 * ‖Q‖ ^ 2 + 2 * ‖D - Z t‖ ^ 2 := by
      have hnonneg1 := norm_nonneg (U - Z t)
      have hnonneg2 := norm_nonneg (U - D)
      have hnonneg3 := norm_nonneg (D - Z t)
      have hnonneg4 := norm_nonneg Q
      nlinarith [sq_nonneg (3 * ‖Q‖ - ‖D - Z t‖)]
    have hvar := norm_resolvent_martingale_sub_limit_sq hP hcoord f Z hZ n t
    change ‖D - Z t‖ ^ 2 = (t : ℝ) * E n at hvar
    have hmul := mul_le_mul_of_nonneg_left hsq ha.le
    change (a : ℝ) * ‖U - Z t‖ ^ 2 ≤ 18 * R n + 2 * E n
    dsimp only [R]
    change (a : ℝ) * ‖U - Z t‖ ^ 2 ≤ 18 * ((a : ℝ) * ‖Q‖ ^ 2) + 2 * E n
    rw [hvar] at hmul
    calc
      _ ≤ (a : ℝ) * (18 * ‖Q‖ ^ 2 + 2 * ((t : ℝ) * E n)) := hmul
      _ = 18 * ((a : ℝ) * ‖Q‖ ^ 2) + 2 * (((a : ℝ) * t) * E n) := by ring
      _ = _ := by rw [hat, one_mul]
  · exact hupper

end EinsteinFull.External.DFGW
