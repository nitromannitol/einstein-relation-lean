import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic

/-! Restated from the library module `EinsteinRelation.Environment.MatrixNorm`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open scoped BigOperators
namespace EinsteinRelation
/-- Sum of squares of every matrix entry. -/
def frobeniusSq {d : ℕ} (A : Mat d) : ℝ := ∑ i, ∑ j, A i j * A i j
/-- Euclidean (Frobenius) norm of a matrix, with no new matrix norm instance. -/
noncomputable def frobeniusNorm {d : ℕ} (A : Mat d) : ℝ := Real.sqrt (frobeniusSq A)
end EinsteinRelation
