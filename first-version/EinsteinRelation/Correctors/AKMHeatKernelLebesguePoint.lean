import EinsteinRelation.External.AKMHeatKernel
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The open-ball interpretation of the kernel initial condition

Source: AKM Proposition E.1, (E.11), p. 501; `paper/main.tex:850`.
The closed-ball formulation agrees with the source's open-ball averages.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM

/-- Removing the sphere does not change any positive-radius average. -/
theorem akm_average_closedBall_eq_ball {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    {r : ℝ} (hr : 0 < r) :
    (⨍ z in Metric.closedBall x r, f z ∂volume) =
      ⨍ z in Metric.ball x r, f z ∂volume := by
  apply setAverage_congr
  have hs : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      z ∉ Metric.sphere x r := by
    exact (measure_eq_zero_iff_ae_notMem).mp
      (Measure.addHaar_sphere_of_ne_zero volume x hr.ne')
  filter_upwards [hs] with z hz
  apply propext
  change dist z x ≤ r ↔ dist z x < r
  change dist z x ≠ r at hz
  exact ⟨fun h => lt_of_le_of_ne h hz, fun h => h.le⟩

/-- The candidate's Lebesgue-point condition is exactly the open Euclidean
ball condition used in AKM (E.11), p. 501. -/
theorem akm_isHeatKernelLebesguePoint_iff_openBall {d : ℕ}
    (f : Vec d → ℝ) (y : Vec d) :
    IsHeatKernelLebesguePoint f y ↔
      Tendsto (fun r : ℝ =>
        ⨍ z in Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
          |f (WithLp.ofLp z) - f y| ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  apply tendsto_congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact akm_average_closedBall_eq_ball _ _ hr

/-- The coordinate and Euclidean-space open-ball averages coincide exactly. -/
theorem akm_average_heatKernelBall {d : ℕ} (f : Vec d → ℝ)
    (y : Vec d) (r : ℝ) :
    (⨍ z in heatKernelBall y r, f z ∂volume) =
      ⨍ z in Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
        f (WithLp.ofLp z) ∂volume := by
  have hpre : (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹'
      heatKernelBall y r = Metric.ball (WithLp.toLp 2 y) r := by
    ext z
    simp only [Set.mem_preimage, heatKernelBall, Set.mem_setOf_eq,
      TimeChange.euclideanNorm_eq_norm_toLp, Metric.mem_ball, dist_eq_norm]
    rfl
  have he : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
    (MeasurableEquiv.toLp 2 (Vec d)).symm.measurableEmbedding
  have hvol : volume (heatKernelBall y r) =
      volume (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r) := by
    rw [← hpre]
    exact ((PiLp.volume_preserving_ofLp (Fin d)).measure_preimage_emb he _).symm
  simp only [setAverage_eq, Measure.real, hvol]
  congr 1
  exact ((PiLp.volume_preserving_ofLp (Fin d)).setIntegral_preimage_emb he f
    (heatKernelBall y r)).symm.trans (by rw [hpre])

/-- Exact source formulation of the Lebesgue-point condition, on the
coordinate carrier and with the Euclidean open balls of Appendix E. -/
theorem akm_isHeatKernelLebesguePoint_iff_source {d : ℕ}
    (f : Vec d → ℝ) (y : Vec d) :
    IsHeatKernelLebesguePoint f y ↔
      Tendsto (fun r : ℝ => ⨍ z in heatKernelBall y r, |f z - f y| ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  rw [akm_isHeatKernelLebesguePoint_iff_openBall]
  simp_rw [akm_average_heatKernelBall]

end EinsteinRelation.Correctors
