import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic

/-! Vocabulary for `EinsteinFull.Frozen.StructuralData`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull

/-- The deterministic data in Section 1, including the dimension parameter; the derivative sequence is indexed
by natural numbers and its zeroth value is unused. -/
structure StructuralData (dimension : ℕ) where
  ellipticity : ℝ
  dependenceRange : ℝ
  derivativeBound : ℕ → ℝ
  one_le_ellipticity : 1 ≤ ellipticity
  one_le_dependenceRange : 1 ≤ dependenceRange
  derivativeBound_pos : ∀ k : ℕ, 1 ≤ k → 0 < derivativeBound k

end EinsteinFull
