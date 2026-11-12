import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EllipticOperatorBound
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Bounds

/-! Restated from the library module `EinsteinRelation.Environment.SourceReducedBoundSupport`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

namespace EinsteinRelation
/-- A concrete value of the reduced-field bound `Λ(L)` in
`paper/main.tex`, equation `eq.reduced-bounds`, depending only on the original
coefficient and potential bound `L`. -/
noncomputable def sourceReducedBound (L : ℝ) : ℝ :=
  Real.exp (2 * L) * (3 * L^2 + L + 1)
end EinsteinRelation
