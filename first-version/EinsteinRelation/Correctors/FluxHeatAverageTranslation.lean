import EinsteinRelation.Correctors.HeatAverageTranslation

/-! Source: `paper/main.tex:724-731`. Translate the matrix-valued heat gauge
entrywise, then retain the Frobenius norm in the local oscillation. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Spatial translation commutes with the actual matrix-valued heat average. -/
theorem fluxHeatAverage_translation {d : ℕ} (S : Vec d → Mat d) (z : Vec d) (r : ℝ) :
    fluxHeatAverage (fun y => S (y + z)) 0 r = fluxHeatAverage S z r := by
  ext j k
  exact scalarHeatAverage_translation (fun y => S y j k) z r

/-- The Frobenius oscillation and its heat center translate together. -/
theorem flux_ball_heat_oscillation_translate {d : ℕ} (S : Vec d → Mat d)
    (z : Vec d) (r : ℝ) :
    (⨍ x in ball z r, frobeniusNorm (S x - fluxHeatAverage S z r) ^ 2 ∂volume) =
      (⨍ x in ball 0 r, frobeniusNorm (S (x + z) -
        fluxHeatAverage (fun y => S (y + z)) 0 r) ^ 2 ∂volume) := by
  rw [setAverage_ball_translation, fluxHeatAverage_translation]

end EinsteinRelation.Correctors
