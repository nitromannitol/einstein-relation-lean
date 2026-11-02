import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic

/-! Vocabulary for `EinsteinRelation.Correctors.HeatSmoothing`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

/-- The Euclidean heat kernel of `e^{tΔ}` at time `t > 0`, `(4πt)^{-d/2} exp(-|x|²/(4t))`
(`paper/main.tex:961`, convolution with the Euclidean heat kernel at time `t`). -/
def euclideanHeatKernel {d : ℕ} (t : ℝ) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(euclideanSq x) / (4 * t))

end EinsteinRelation.Correctors

end
