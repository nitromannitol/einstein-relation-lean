import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

private theorem positive_norm_eq_moment {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v : X → ℝ) {p : ℝ} (hv : MemLp v (ENNReal.ofReal p) μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ v x)
    (hp : 0 < p) :
    eLpNorm v (ENNReal.ofReal p) μ =
      (ENNReal.ofReal (∫ x, Real.rpow (v x) p ∂μ)) ^ (1 / p) := by
  have hi : Integrable (fun x => Real.rpow (v x) p) μ := by
    have h := hv.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal hp.le] at h
    apply h.congr
    filter_upwards [hpos] with x hx
    simp [Real.norm_eq_abs, abs_of_nonneg hx]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    ENNReal.ofReal_ne_top hv.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal hi]
  · apply lintegral_congr_ae
    filter_upwards [hpos] with x hx
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
    simp [Real.norm_eq_abs, abs_of_nonneg hx]
  · filter_upwards [hpos] with x hx
    exact Real.rpow_nonneg hx _

/-- Positive Lp norms converge when a nonnegative vanishing constant is removed. -/
theorem c20_regularized_positive_eLpNorm_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (u : X → ℝ) (hu0 : ∀ᵐ x ∂μ, 0 ≤ u x)
    (p : ℝ) (hp : 0 < p) (hu : MemLp u (ENNReal.ofReal p) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => u x + ε n) (ENNReal.ofReal p) μ) atTop
      (𝓝 (eLpNorm u (ENNReal.ofReal p) μ)) := by
  have hm (e : ℝ) : MemLp (fun x => u x + e) (ENNReal.ofReal p) μ :=
    hu.add (memLp_const e)
  have hi : Integrable (fun x => Real.rpow (u x + 1) p) μ := by
    have h := (hm 1).integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal hp.le] at h
    apply h.congr
    filter_upwards [hu0] with x hx
    simp [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ u x + 1 by linarith)]
  have hevent : ∀ᶠ n in atTop, ε n ≤ 1 :=
    hε0.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlim : Tendsto (fun n => ∫ x, Real.rpow (u x + ε n) p ∂μ) atTop
      (𝓝 (∫ x, Real.rpow (u x) p ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => Real.rpow (u x + 1) p)
    · exact Eventually.of_forall fun n => (((hu.aestronglyMeasurable.add_const (ε n)).aemeasurable.pow_const p)).aestronglyMeasurable
    · filter_upwards [hevent] with n hn
      filter_upwards [hu0] with x hx
      change |(u x + ε n) ^ p| ≤ (u x + 1) ^ p
      rw [abs_of_nonneg (Real.rpow_nonneg (by linarith [hε n]) p)]
      exact Real.rpow_le_rpow (by linarith [hε n]) (by linarith) hp.le
    · exact hi
    · filter_upwards [] with x
      have ht : Tendsto (fun n => u x + ε n) atTop (𝓝 (u x)) := by
        simpa using tendsto_const_nhds.add hε0
      exact (Real.continuous_rpow_const hp.le |>.tendsto _).comp ht
  rw [positive_norm_eq_moment μ u hu hu0 hp]
  have heq (n : ℕ) := positive_norm_eq_moment μ (fun x => u x + ε n)
    (hm (ε n)) (hu0.mono fun x hx => by linarith [hε n]) hp
  simp_rw [heq]
  exact (ENNReal.continuous_rpow_const.tendsto _).comp
    ((ENNReal.continuous_ofReal.tendsto _).comp hlim)

end EinsteinFull.Calculus

