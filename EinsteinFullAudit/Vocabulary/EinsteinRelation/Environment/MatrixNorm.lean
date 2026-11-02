import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic

/-! Vocabulary for `EinsteinRelation.Environment.MatrixNorm`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open scoped BigOperators

namespace EinsteinRelation

/-- Sum of squares of every matrix entry. -/
def frobeniusSq {d : ℕ} (A : Mat d) : ℝ := ∑ i, ∑ j, A i j * A i j

/-- Euclidean (Frobenius) norm of a matrix, with no new matrix norm instance. -/
noncomputable def frobeniusNorm {d : ℕ} (A : Mat d) : ℝ := Real.sqrt (frobeniusSq A)

end EinsteinRelation
