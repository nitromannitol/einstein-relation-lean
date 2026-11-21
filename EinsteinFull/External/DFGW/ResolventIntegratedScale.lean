import EinsteinFull.External.DFGW.ResolventNormScale
import EinsteinFull.External.DFGW.TimeIntegralBound
import EinsteinFull.External.DFGW.MeanSquareConvergence

/-! # Normalized time-integrated resolvents

The integrated absolute reciprocal resolvent, multiplied by its parameter and diffusive
normalization, vanishes in mean square and in probability.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The normalized time integral of the absolute reciprocal resolvent vanishes in probability. -/
theorem tendstoInMeasure_normalized_integrated_resolvent_abs
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    TendstoInMeasure P (fun (n : ℕ) η => (Real.sqrt (n + 1))⁻¹ *
      (reciprocalShift n : ℝ) *
        ∫ u in (0 : ℝ)..(n + 1 : ℝ), |transitionResolvent hP (reciprocalShift n) f (η u)|)
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let F (n : ℕ) (η : C(ℝ, S)) : ℝ := (Real.sqrt (n + 1))⁻¹ *
    (reciprocalShift n : ℝ) *
      ∫ u in (0 : ℝ)..(n + 1 : ℝ), |transitionResolvent hP (reciprocalShift n) f (η u)|
  let R (n : ℕ) : Lp ℝ 2 μ := transitionResolvent hP (reciprocalShift n) f
  have hM (n : ℕ) : MemLp (F n) 2 P := by
    have h := (time_integral_memLp_and_sq_le hP (fun x => |R n x|) (Lp.memLp (R n)).abs
      (show (0 : ℝ) ≤ n + 1 by positivity)).1
    exact h.const_mul _
  have hnorm (n : ℕ) : (∫ x, |R n x| ^ 2 ∂μ) = ‖R n‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, ← pow_two, sq_abs]
  have hbound (n : ℕ) : (∫ η, F n η ^ 2 ∂P) ≤
      (reciprocalShift n : ℝ) * ‖R n‖ ^ 2 := by
    have ht : 0 ≤ (n + 1 : ℝ) := by positivity
    have hb := (time_integral_memLp_and_sq_le hP (fun x => |R n x|) (Lp.memLp (R n)).abs ht).2
    rw [hnorm] at hb
    have hfactor : ((Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ)) ^ 2 *
        (n + 1 : ℝ) ^ 2 = (reciprocalShift n : ℝ) := by
      change ((Real.sqrt (n + 1))⁻¹ * (1 / (n + 1 : ℝ))) ^ 2 *
        (n + 1 : ℝ) ^ 2 = 1 / (n + 1 : ℝ)
      have hs : (Real.sqrt (n + 1)) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt ht
      have hsne : Real.sqrt (n + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
      have hnne : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith
    calc
      (∫ η, F n η ^ 2 ∂P) = ((Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ)) ^ 2 *
          ∫ η, (∫ u in (0 : ℝ)..(n + 1 : ℝ), |R n (η u)|) ^ 2 ∂P := by
        simp only [F, R, mul_pow, integral_const_mul]
      _ ≤ ((Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ)) ^ 2 *
          ((n + 1 : ℝ) ^ 2 * ‖R n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = (reciprocalShift n : ℝ) * ‖R n‖ ^ 2 := by rw [← mul_assoc, hfactor]
  have hlim : Tendsto (fun n : ℕ => ∫ η, F n η ^ 2 ∂P) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) hbound
    exact tendsto_reciprocalShift_mul_resolvent_norm_sq hP f hint
  exact tendstoInMeasure_zero_of_integral_sq F hM hlim

end EinsteinFull.External.DFGW
