import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic

/-! Restated from the library module `EinsteinRelation.Sharpness.NoiseKernel`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
open scoped Distributions
namespace EinsteinRelation.Sharpness
/-- Actual smooth compactly supported scalar tests on the coordinate space. -/
abbrev NoiseTest (d : ℕ) := TestFunction (⊤ : TopologicalSpace.Opens (Vec d)) ℝ ⊤
/-- Actual scalar distributions on the LF test-function space. -/
abbrev NoiseSample (d : ℕ) := Distribution (⊤ : TopologicalSpace.Opens (Vec d)) ℝ ⊤
end EinsteinRelation.Sharpness
