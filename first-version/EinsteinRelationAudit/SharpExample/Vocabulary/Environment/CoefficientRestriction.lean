import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Reduction

/-! Restated from the library module `EinsteinRelation.Environment.CoefficientRestriction`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

namespace EinsteinRelation
/-- Canonical continuous matrix fields, with the compact-open Borel structure. -/
abbrev CoefficientField (d : ℕ) := C(Vec d, Mat d)
instance (d : ℕ) : MeasurableSpace (CoefficientField d) := borel (CoefficientField d)
instance (d : ℕ) : BorelSpace (CoefficientField d) := ⟨rfl⟩
/-- The actual reduced matrix field of a physical environment. -/
noncomputable def reducedMatrixField {d : ℕ} (ω : FieldPair d) : CoefficientField d :=
  (reduce ω).1
end EinsteinRelation
