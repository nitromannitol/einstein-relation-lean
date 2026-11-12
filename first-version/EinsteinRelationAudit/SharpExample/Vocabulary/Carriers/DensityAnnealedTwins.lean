import Mathlib.Probability.Distributions.Exponential
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Reduction
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ValidAnnealedLawSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.Coupling

/-! Restated from the library module `EinsteinRelation.Carriers.DensityAnnealedTwins`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EinsteinRelation.Carriers
/-- The reduced coefficient and clock law induced by the physical environment law.
Production twin of `EinsteinRelation.Frozen.DensityCarriers.reducedReferenceLaw`
(`EinsteinRelation/Frozen/DensityCarriers/ReducedReferenceLaw.lean`), with the same body. -/
def reducedReferenceLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : Measure (FieldPair d) :=
  Measure.map reduce Q.measure
/-- The reduced environment observed at time `t` along a continuous path.
Production twin of `EinsteinRelation.Frozen.DensityCarriers.reducedObservationAt`
(`EinsteinRelation/Frozen/DensityCarriers/ReducedObservationAt.lean`), with the same body. -/
def reducedObservationAt {d : ℕ} (t : ℝ≥0)
    (z : FieldPair d × Path d) : FieldPair d :=
  reduce (translate (pathPosition t z.2) z.1)
open EinsteinRelation.Probability.ValidAnnealedLawSupport
/-- The annealed joint environment and physical path law at the origin.
Production twin of `EinsteinRelation.Frozen.ValidAnnealedLawCarriers.annealedCoordinateJoint`
(`EinsteinRelation/Frozen/ValidAnnealedLawCarriers/AnnealedCoordinateJoint.lean`), with the
coordinate-path input replaced by its fields `Q`, `P`, `origin_probability`. -/
def annealedCoordinateJoint {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) :
    Measure (FieldPair d × Path d) :=
  annealedJointOnProbabilityFibers Q (originLaw P) origin_probability
end EinsteinRelation.Carriers
