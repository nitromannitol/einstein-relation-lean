import EinsteinRelation.Correctors.HeatAverageDilation
import Mathlib.MeasureTheory.Group.Integral

/-! Source: `paper/main.tex:718-723`. Translate both the heat center and the spatial ball. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Spatial translations commute with the scalar heat average. -/
theorem scalarHeatAverage_translation {d : ℕ} (u : Vec d → ℝ) (z : Vec d) (r : ℝ) :
    scalarHeatAverage (fun y => u (y + z)) 0 r = scalarHeatAverage u z r := by
  unfold scalarHeatAverage
  have h := (measurePreserving_add_right (volume : Measure (Vec d)) z).integral_comp
    (Homeomorph.addRight z).measurableEmbedding (fun y => heatKernel z r y * u y)
  simpa only [heatKernel, add_sub_cancel_right, sub_zero] using h

/-- Translation carries a centered ball average to the origin ball average. -/
theorem setAverage_ball_translation {d : ℕ} (f : Vec d → ℝ) (z : Vec d) (r : ℝ) :
    (⨍ x in ball z r, f x ∂volume) =
      ⨍ x in ball 0 r, f (x + z) ∂volume := by
  have hpre : (fun x : Vec d => x + z) ⁻¹' ball z r = ball 0 r := by
    ext x
    simp only [Set.mem_preimage, ball, Set.mem_setOf_eq, add_sub_cancel_right, sub_zero]
  have hmp := measurePreserving_add_right (volume : Measure (Vec d)) z
  have hi := hmp.setIntegral_preimage_emb
    (Homeomorph.addRight z).measurableEmbedding f (ball z r)
  rw [hpre] at hi
  have hmeas : MeasurableSet (ball z r) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hm := hmp.measure_preimage hmeas.nullMeasurableSet
  rw [hpre] at hm
  simp only [setAverage_eq, measureReal_def, hm, hi]

/-- Both the squared local oscillation and its heat gauge translate exactly. -/
theorem scalar_ball_heat_oscillation_translate {d : ℕ} (u : Vec d → ℝ)
    (z : Vec d) (r : ℝ) :
    (⨍ x in ball z r, |u x - scalarHeatAverage u z r| ^ 2 ∂volume) =
      (⨍ x in ball 0 r, |u (x + z) -
        scalarHeatAverage (fun y => u (y + z)) 0 r| ^ 2 ∂volume) := by
  rw [setAverage_ball_translation, scalarHeatAverage_translation]

end EinsteinRelation.Correctors
