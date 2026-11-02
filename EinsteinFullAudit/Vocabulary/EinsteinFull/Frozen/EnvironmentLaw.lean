import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic

/-! Vocabulary for `EinsteinFull.Frozen.EnvironmentLaw`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull

/-- Assumption 1.1, reusing the blueprint's exact joint field-law carrier. -/
abbrev EnvironmentLaw (d : ℕ) (Λ₀ r₀ : ℝ) :=
  EinsteinRelation.EnvironmentLaw d Λ₀ r₀

end EinsteinFull
