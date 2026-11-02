import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic

/-! Vocabulary for `EinsteinRelation.Sharpness.NoiseKernel`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

open scoped Distributions

namespace EinsteinRelation.Sharpness

/-- Actual smooth compactly supported scalar tests on the coordinate space. -/
abbrev NoiseTest (d : ℕ) := TestFunction (⊤ : TopologicalSpace.Opens (Vec d)) ℝ ⊤

/-- Actual scalar distributions on the LF test-function space. -/
abbrev NoiseSample (d : ℕ) := Distribution (⊤ : TopologicalSpace.Opens (Vec d)) ℝ ⊤

end EinsteinRelation.Sharpness
