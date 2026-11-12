import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Kernel.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.HorizontalSobolev
import EinsteinRelationAudit.MobilityRate.Vocabulary.Carriers.DensityAnnealedTwins
import EinsteinRelationAudit.MobilityRate.Vocabulary.Clock.PhysicalClock
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EllipticOperatorBound
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.HeatSmoothing
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.StationarySpatialRealizationSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.ClockInverseSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.GMPFamily
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Reduction
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.SourceReducedBoundSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GMPPhysicalInputs
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GMPReducedInputs
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.LocalSigma
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.ReductionLocality

/-! Restated from the library module `EinsteinRelation.Mobility.VelocityRateFromSteps`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory Filter
open scoped ENNReal Topology
namespace EinsteinRelation
open EinsteinRelation.Correctors
open EinsteinRelation.Correctors.StationarySpatialRealization (spatialRealization)
open EinsteinRelation.Carriers (reducedReferenceLaw)
/-- The index `e₁ = ⟨0, _⟩ : Fin d`, which exists since `2 ≤ d`. -/
def firstIdx {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩
end EinsteinRelation
