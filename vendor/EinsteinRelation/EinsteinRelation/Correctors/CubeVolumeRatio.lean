import EinsteinRelation.Environment.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
/-- Enlarging a growing coordinate cube by a fixed radius has asymptotically
unit volume ratio; source `paper/main.tex:693-698`. -/
theorem tendsto_cube_volume_ratio (d : ℕ) (S : ℝ) :
    Tendsto (fun R : ℝ => volume.real (Metric.closedBall (0 : Vec d) (R + S)) /
      volume.real (Metric.closedBall (0 : Vec d) R)) atTop (𝓝 1) := by
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hS : Tendsto (fun R : ℝ => S / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have ht : Tendsto (fun R : ℝ => (1 + S / R) ^ d) atTop (𝓝 1) := by
    simpa using (hc.add hS).pow d
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-S)] with R hR hRS
  show (1 + S / R) ^ d = volume.real (Metric.closedBall (0 : Vec d) (R + S)) /
    volume.real (Metric.closedBall (0 : Vec d) R)
  have hpos : 0 < R + S := by linarith
  have hv (r : ℝ) (hr : 0 ≤ r) :
      volume.real (Metric.closedBall (0 : Vec d) r) = (2 * r) ^ d := by
    have h2 : (0 : ℝ) ≤ 2 * r := by linarith
    rw [Measure.real, Real.volume_pi_closedBall _ hr,
      ENNReal.toReal_ofReal (pow_nonneg h2 _)]
    simp
  rw [hv R hR.le, hv (R + S) hpos.le, ← div_pow]
  congr 1
  field_simp
end EinsteinRelation.Correctors
