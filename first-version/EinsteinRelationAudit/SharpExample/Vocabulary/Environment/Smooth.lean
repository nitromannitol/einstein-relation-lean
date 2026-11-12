import Mathlib.Analysis.Calculus.ContDiff.Defs
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic

/-! Restated from the library module `EinsteinRelation.Environment.Smooth`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

namespace EinsteinRelation
/-- The physical matrix entries and potential are smooth on all of space. -/
def IsSmoothFieldPair {d : ℕ} (ω : FieldPair d) : Prop :=
  (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.2 x)
end EinsteinRelation
