import EinsteinFull.External.DFGW.ResolventRemainder

/-! # Sublinear resolvent remainder on comparable scales

The Kipnis–Varadhan mean-square remainder is sublinear along any sequence of times comparable
with the reciprocal resolvent parameter.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The normalized mean-square remainder vanishes along any sequence between half and all of
the reciprocal resolvent scale. -/
theorem tendsto_resolvent_remainder_comparable (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (q : ℕ → ℝ≥0)
    (hlower : ∀ n, (1 / 2 : ℝ) ≤ (reciprocalShift n : ℝ) * (q n : ℝ))
    (hupper : ∀ n, (reciprocalShift n : ℝ) * (q n : ℝ) ≤ 1) :
    Tendsto (fun n : ℕ => (q n : ℝ)⁻¹ * ‖timeIntegralLp hP f (q n) - Z (q n)‖ ^ 2)
      atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun n => (reciprocalShift n : ℝ) *
    ‖transitionResolvent hP (reciprocalShift n) f‖ ^ 2
  let E : ℕ → ℝ := fun n => ‖dynkinIncrementLp hP
    (transitionResolventDomain hP (reciprocalShift n) f) 1 - Z 1‖ ^ 2
  have hR : Tendsto R atTop (𝓝 0) := tendsto_reciprocalShift_mul_resolvent_norm_sq hP f hint
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := ((hZ 1).sub_const (Z 1)).norm.pow 2
    simpa [E] using h
  have hlim : Tendsto (fun n : ℕ => 36 * R n + 4 * E n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hR.const_mul 36).add (hE.const_mul 4)
  apply squeeze_zero (g := fun n : ℕ => 36 * R n + 4 * E n)
  · intro n
    exact mul_nonneg (inv_nonneg.mpr (q n).coe_nonneg) (sq_nonneg _)
  · intro n
    let t := q n
    let a := reciprocalShift n
    let U := timeIntegralLp hP f t
    let D := dynkinIncrementLp hP (transitionResolventDomain hP a f) t
    let Q := transitionResolvent hP a f
    have ha : 0 < (a : ℝ) := a.2
    have hlo : (1 / 2 : ℝ) ≤ (a : ℝ) * t := hlower n
    have hhi : (a : ℝ) * t ≤ 1 := hupper n
    have ht : 0 < (t : ℝ) := by
      by_contra h
      have hzero : (t : ℝ) = 0 := le_antisymm (le_of_not_gt h) t.coe_nonneg
      simp only [hzero, mul_zero] at hlo
      norm_num at hlo
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
    change ‖D - Z t‖ ^ 2 = (t : ℝ) * E n at hvar
    have hscaled := mul_le_mul_of_nonneg_left hsq ha.le
    rw [hvar] at hscaled
    have hscale : (a : ℝ) * ‖U - Z t‖ ^ 2 ≤ 18 * R n + 2 * E n := by
      have hE0 : 0 ≤ E n := sq_nonneg _
      have hprod : ((a : ℝ) * (t : ℝ)) * E n ≤ E n := by nlinarith
      dsimp only [R]
      change (a : ℝ) * ‖U - Z t‖ ^ 2 ≤ 18 * ((a : ℝ) * ‖Q‖ ^ 2) + 2 * E n
      calc
        _ ≤ (a : ℝ) * (18 * ‖Q‖ ^ 2 + 2 * ((t : ℝ) * E n)) := hscaled
        _ = 18 * ((a : ℝ) * ‖Q‖ ^ 2) + 2 * (((a : ℝ) * t) * E n) := by ring
        _ ≤ _ := by linarith
    have hratio := mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖U - Z t‖)
    change (t : ℝ)⁻¹ * ‖U - Z t‖ ^ 2 ≤ 36 * R n + 4 * E n
    nlinarith
  · exact hlim

end EinsteinFull.External.DFGW
