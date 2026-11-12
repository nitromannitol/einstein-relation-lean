import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic

/-! Restated from the library module `EinsteinRelation.Correctors.HeatSmoothing`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
/-- The Euclidean heat kernel of `e^{tΔ}` at time `t > 0`, `(4πt)^{-d/2} exp(-|x|²/(4t))`
(`paper/main.tex:971`, convolution with the Euclidean heat kernel at time `t`). -/
def euclideanHeatKernel {d : ℕ} (t : ℝ) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(euclideanSq x) / (4 * t))
end EinsteinRelation.Correctors
end
