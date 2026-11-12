import EinsteinRelation.Correctors.AKMHeatKernelLebesguePoint

open MeasureTheory Filter
namespace EinsteinRelation.Correctors
open External.AKM

/-- A continuous datum satisfies the normalized initial-trace condition
at every point. Source: `paper/main.tex:850`; AKM (E.11). -/
theorem akm_continuous_isHeatKernelLebesguePoint {d : ℕ}
    {f : Vec d → ℝ} {y : Vec d} (hf : ContinuousAt f y) :
    IsHeatKernelLebesguePoint f y := by
  unfold IsHeatKernelLebesguePoint
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp hf (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hbound : ∀ z ∈ Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
      |f (WithLp.ofLp z) - f y| ≤ ε / 2 := by
    intro z hz
    have hcoord : dist (WithLp.ofLp z) y ≤ dist z (WithLp.toLp 2 y) := by
      rw [dist_pi_le_iff dist_nonneg]
      intro i
      have h1 : ‖(z - WithLp.toLp 2 y) i‖ ≤ dist z (WithLp.toLp 2 y) := by
        rw [dist_eq_norm]
        exact PiLp.norm_apply_le (z - WithLp.toLp 2 y) i
      have h3 : dist (WithLp.ofLp z i) (y i) = ‖(z - WithLp.toLp 2 y) i‖ := by
        rw [Real.dist_eq, Real.norm_eq_abs]
        rfl
      rw [h3]
      exact h1
    have hlt : dist (WithLp.ofLp z) y < δ :=
      lt_of_le_of_lt hcoord (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr.2)
    have h2 := hfδ hlt
    rw [Real.dist_eq] at h2
    exact h2.le
  have hpos : 0 < volume.real (Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r) := by
    rw [Measure.real]
    exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ hr.1).ne'
      measure_closedBall_lt_top.ne
  have hint : ‖∫ z in Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
      |f (WithLp.ofLp z) - f y| ∂volume‖ ≤
        ε / 2 * volume.real (Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r) := by
    apply norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top
    intro z hz
    rw [Real.norm_eq_abs, abs_abs]
    exact hbound z hz
  have hint' : (∫ z in Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
      |f (WithLp.ofLp z) - f y| ∂volume) ≤
        ε / 2 * volume.real (Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r) :=
    le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hint)
  have hnn : 0 ≤ ⨍ z in Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
      |f (WithLp.ofLp z) - f y| ∂volume := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hpos.le) (integral_nonneg fun z => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, setAverage_eq, smul_eq_mul]
  have hne := hpos.ne'
  calc (volume.real (Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r))⁻¹ *
        (∫ z in Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
          |f (WithLp.ofLp z) - f y| ∂volume)
      ≤ (volume.real (Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r))⁻¹ *
          (ε / 2 * volume.real (Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r)) :=
        mul_le_mul_of_nonneg_left hint' (inv_nonneg.mpr hpos.le)
    _ = ε / 2 := by rw [mul_comm (ε / 2), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ < ε := by linarith

end EinsteinRelation.Correctors
