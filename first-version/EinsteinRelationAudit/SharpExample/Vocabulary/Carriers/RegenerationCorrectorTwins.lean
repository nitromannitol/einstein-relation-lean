import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.Generator
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.HorizontalSobolev
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.StationaryGradientDomainSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Bounds
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.CoefficientRestriction
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.LocalSigma
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ReductionLocality
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.Coupling

/-! Restated from the library module `EinsteinRelation.Carriers.RegenerationCorrectorTwins`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Carriers
section CycleConditioning
open EinsteinRelation.Regeneration
/-- The source no-backtracking event on the actual annealed environment/sample space.
Mirrors `EinsteinRelation/Frozen/Regeneration/CycleConditioningEvent.lean`. -/
def cycleConditioningEvent {d : ℕ} (hd : 2 ≤ d) (R : ℝ) :
    Set (FieldPair d × CoupledSample d) :=
  {ωz | NoBacktracking R ωz.2.1 ⟨0, by omega⟩}
/-- The literal law conditioned on the actual no-backtracking event, with its positive
mass explicit. Mirrors `EinsteinRelation/Frozen/Regeneration/CycleConditionedLaw.lean`. -/
noncomputable def cycleConditionedLaw {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (hd : 2 ≤ d) (R : ℝ)
    (hD : (annealedCoupledLaw Q K) (cycleConditioningEvent hd R) ≠ 0) :
    {μ : Measure (FieldPair d × CoupledSample d) // IsProbabilityMeasure μ} := by
  letI : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  exact ⟨ProbabilityTheory.cond (annealedCoupledLaw Q K) (cycleConditioningEvent hd R),
    ProbabilityTheory.cond_isProbabilityMeasure hD⟩
end CycleConditioning
/-- The homogenized coefficient column, the expected corrector flux.
Mirrors `EinsteinRelation/Frozen/Correctors/HomogenizedCoefficientColumn.lean`. -/
noncomputable def homogenizedCoefficientColumn
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  EinsteinRelation.Correctors.expectedCorrectorFlux Q i
end EinsteinRelation.Carriers
