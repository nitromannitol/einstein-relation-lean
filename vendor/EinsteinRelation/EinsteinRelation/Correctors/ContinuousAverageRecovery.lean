import EinsteinRelation.Correctors.MeasurableRegularRepresentative
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Source: `paper/main.tex:688-702,754-758`. Shrinking averages
recover continuous local versions of a spatial volume class. -/
open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Shrinking averages recover the continuous version at every point
strictly inside its domain, even when the input is only equal a.e. -/
theorem tendsto_local_average_of_continuousOn_ae {d : ℕ}
    (f v : Vec d → ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (hv : ContinuousOn v U) (heq : f =ᵐ[volume.restrict U] v)
    (x : Vec d) (hx : x ∈ U) :
    Tendsto (fun n : ℕ => ⨍ z in Metric.ball (0 : Vec d) (((n : ℝ) + 1)⁻¹),
      f (x + z) ∂volume) atTop (𝓝 (v x)) := by
  have hfve := (measurePreserving_add_left volume x).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU.measurableSet).mp heq)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hvη⟩ := Metric.continuousAt_iff.mp
    (hv.continuousAt (hU.mem_nhds hx)) (ε / 2) (half_pos hε)
  have hsmall : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1)⁻¹ < min δ η := by
    apply (tendsto_order.1 hr).2
    exact lt_min hδ hη
  filter_upwards [hsmall] with n hn
  let r : ℝ := ((n : ℝ) + 1)⁻¹
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := lt_of_lt_of_le hn (min_le_left _ _)
  have hrη : r < η := lt_of_lt_of_le hn (min_le_right _ _)
  have hdist (z : Vec d) : dist (x + z) x = ‖z‖ := by
    simp only [dist_eq_norm, add_sub_cancel_left]
  have hsub : (fun z : Vec d => x + z) '' Metric.closedBall 0 r ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    apply hδU
    rw [Metric.mem_ball, hdist]
    exact (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz : ‖z‖ ≤ r).trans_lt hrδ
  have hvc : ContinuousOn (fun z : Vec d => v (x + z)) (Metric.closedBall 0 r) :=
    hv.comp (continuous_const.add continuous_id).continuousOn (fun z hz => hsub ⟨z, hz, rfl⟩)
  have hvi : IntegrableOn (fun z : Vec d => v (x + z)) (Metric.ball 0 r) volume :=
    (hvc.integrableOn_compact (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Vec d) r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hvol : 0 < volume.real (Metric.ball (0 : Vec d) r) :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 hrpos)) measure_ball_ne_top
  have havgeq : (⨍ z in Metric.ball (0 : Vec d) r, f (x + z)) =
      ⨍ z in Metric.ball (0 : Vec d) r, v (x + z) := by
    apply average_congr
    filter_upwards [ae_restrict_of_ae hfve, ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with z hz hzm
    apply hz
    apply hδU
    rw [Metric.mem_ball, hdist]
    have hzball : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hzm
    exact hzball.trans hrδ
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Vec d) r),
      ‖v (x + z) - v x‖ ≤ ε / 2 := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    have hz' : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact le_of_lt (by simpa only [dist_eq_norm] using hvη ((hdist z).trans_lt (hz'.trans hrη)))
  have hint := norm_integral_le_of_norm_le_const hbound
  have havg : (⨍ z in Metric.ball (0 : Vec d) r, v (x + z)) - v x =
      (volume.real (Metric.ball (0 : Vec d) r))⁻¹ *
        ∫ z in Metric.ball (0 : Vec d) r, (v (x + z) - v x) := by
    rw [integral_sub hvi (integrable_const _), setAverage_eq, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    have hv0 : (volume (Metric.ball (0 : Vec d) r)).toReal ≠ 0 := hvol.ne'
    field_simp
  change dist (⨍ z in Metric.ball (0 : Vec d) r, f (x + z)) (v x) < ε
  rw [havgeq, dist_eq_norm, havg, norm_mul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hvol)]
  have hint' : ‖∫ z in Metric.ball (0 : Vec d) r, (v (x + z) - v x)‖ ≤
      (ε / 2) * volume.real (Metric.ball (0 : Vec d) r) := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using hint
  calc
    (volume.real (Metric.ball (0 : Vec d) r))⁻¹ *
        ‖∫ z in Metric.ball (0 : Vec d) r, (v (x + z) - v x)‖
        ≤ (volume.real (Metric.ball (0 : Vec d) r))⁻¹ *
          ((ε / 2) * volume.real (Metric.ball (0 : Vec d) r)) :=
      mul_le_mul_of_nonneg_left hint' (inv_pos.mpr hvol).le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

end EinsteinRelation.Correctors
