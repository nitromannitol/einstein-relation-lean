import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.StationaryGradientDomainSupport

/-! Restated from the library module `EinsteinRelation.Correctors.StationarySpatialRealizationSupport`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation.Correctors.StationarySpatialRealization
variable {d : ℕ}
/-- Evaluate an L² vector field along the literal translation action. -/
noncomputable def spatialRealization {Q : Measure (FieldPair d)}
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) : Vec d × FieldPair d → EuclideanSpace ℝ (Fin d) :=
  fun p => G (translate p.1 p.2)
end EinsteinRelation.Correctors.StationarySpatialRealization
