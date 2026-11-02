import EinsteinRelation.Correctors.HeatGradientConvolution
import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation of the literal heat-gradient formula

Source: `paper/main.tex:716,748`. Spatial translation shifts the source
and the observation point together, without changing either time cutoff.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Translate both variables of the source density, retaining its signs. -/
theorem akmHeatGradientDensity_translation {d : ℕ} (g : Vec d → Vec d)
    (z : Vec d) (t : ℝ) (j k l : Fin d) (x y : Vec d) :
    akmHeatGradientDensity (fun w => g (w + z)) t j k l x y =
      akmHeatGradientDensity g t j k l (x + z) (y + z) := by
  by_cases ht : 0 < t
  · rw [akmHeatGradientDensity_eq_mixedHessian _ t ht,
      akmHeatGradientDensity_eq_mixedHessian _ t ht]
    simp only [add_sub_add_right_eq_sub]
  · simp only [akmHeatGradientDensity, dif_neg ht]

/-- Translating the source shifts the actual spatial integral. -/
theorem akmHeatGradientSpaceIntegral_translation {d : ℕ} (g : Vec d → Vec d)
    (z : Vec d) (t : ℝ) (j k l : Fin d) (x : Vec d) :
    akmHeatGradientSpaceIntegral (fun w => g (w + z)) t j k l x =
      akmHeatGradientSpaceIntegral g t j k l (x + z) := by
  simp_rw [akmHeatGradientSpaceIntegral, akmHeatGradientDensity_translation]
  exact (measurePreserving_add_right (volume : Measure (Vec d)) z).integral_comp
    (Homeomorph.addRight z).measurableEmbedding _

/-- The two independent truncation endpoints are unchanged by translation. -/
theorem iteratedAKMHeatGradientTruncation_translation {d : ℕ}
    (g : Vec d → Vec d) (z : Vec d) (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation (fun w => g (w + z)) m n j k l x =
      iteratedAKMHeatGradientTruncation g m n j k l (x + z) := by
  simp only [iteratedAKMHeatGradientTruncation,
    akmHeatGradientSpaceIntegral_translation]

end EinsteinRelation.Correctors
