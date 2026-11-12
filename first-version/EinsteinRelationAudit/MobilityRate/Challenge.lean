import Mathlib
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.Generator
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.HorizontalSobolev
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.HorizontalTranslationLp
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.Weak
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.WeightedH1QuotientSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Carriers.DensityAnnealedTwins
import EinsteinRelationAudit.MobilityRate.Vocabulary.Carriers.RegenerationCorrectorTwins
import EinsteinRelationAudit.MobilityRate.Vocabulary.Clock.PhysicalClock
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EllipticOperatorBound
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EuclideanCoordinateCharacterization
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EuclideanCoordinateMoments
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EuclideanLpCoordinateAssembly
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.HeatSmoothing
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.HorizontalH1EuclideanGradient
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.StationaryGradientDomainSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.StationarySpatialRealizationSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.ClockInverseSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.GMPFamily
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.AKMTestIntegralSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Bounds
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.CoefficientRestriction
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.MatrixNorm
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Reduction
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.SourceReducedBoundSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.AKMCorrectorOscillation
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.AKMEnergyDensity
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.AKMHeatKernel
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.AKMKernelSemigroup
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.AKMLocalCorrectors
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GMPLocalityInput
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GMPPhysicalInputs
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GMPReducedInputs
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GantertSection7Support
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GilbargTrudinger
import EinsteinRelationAudit.MobilityRate.Vocabulary.Mobility.AKMFluxDecaySplit
import EinsteinRelationAudit.MobilityRate.Vocabulary.Mobility.QuenchedDriftFromFukushima
import EinsteinRelationAudit.MobilityRate.Vocabulary.Mobility.VelocityRateFromSteps
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.LocalSigma
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.ProbabilityPart
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.ReductionLocality
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.ValidAnnealedLawSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.Regeneration.Construction
import EinsteinRelationAudit.MobilityRate.Vocabulary.Regeneration.Coupling
import EinsteinRelationAudit.MobilityRate.Vocabulary.Regeneration.FirstRewardSteps
import EinsteinRelationAudit.MobilityRate.Vocabulary.Regeneration.OccupationLaterIntervals
import EinsteinRelationAudit.MobilityRate.Vocabulary.Regeneration.RenewalCarriers

/-!
# Theorem 1.2 (paper label `t.main`): Mathlib-only statement

This file states Theorem 1.2 of *Quantitative Einstein relation for reversible diffusions in a
random environment* (Ahmed Bou-Rabee and Ruizhe Xu), the quantitative Einstein relation, together
with every definition that the statement uses. The challenge imports only Mathlib (directly and
through its `Vocabulary/` files). The final theorem has the one intentional `sorry` of the
challenge; `Solution.lean` proves the same theorem from the
library, and the comparator checks that the two statements, and all the definitions they depend
on, are identical.

**The statement.** Assume the 27 literature inputs `h45`, …, `hIP` (see below). Let `d ≥ 2` and
`Λ₀, r₀ ∈ ℝ`. There are `C` and `λ_* > 0` such that, for every environment law `Q` satisfying
Assumption 1.1 with constants `Λ₀` and `r₀` (`EnvironmentLaw d Λ₀ r₀`), every family `P` of
quenched path laws that is the diffusion of Gantert, Mathieu and Piatnitski (2012, Section 7)
for `Q` (`IsGMPPhysicalFamily`), every matrix `Σ_X` for which the unforced diffusion satisfies the
annealed invariance principle with covariance `Σ_X` (`HasDiffusivity`), every `λ ∈ (0, λ_*]`
and every vector `ℓ` that is the quenched velocity of the diffusion with force `λ`
(`HasQuenchedVelocity`), the Euclidean norm of `λ⁻¹ ℓ − Σ_X e₁` is at most `C λ`.

**The hypotheses.** The literature inputs are Prop-valued definitions, restated below with the
docstrings that record their sources: Armstrong, Kuusi and Mourrat (2019) (`h45`, `h46`, `h47`,
`h68`, `h614`, `h615`, `h616`, `hdecay`, `hreg`, `hEll`, `hE1`, `hH2`, `hAKM`), Gilbarg and
Trudinger (2001) (`h832`, `h836`), Fukushima, Oshima and Takeda (2011) (`hFOT`), and Gantert,
Mathieu and Piatnitski (2012) (`hGir`, `hInv`, `hRF`, `hE`, `hTail`, `hLoc`, `hRV`, `hTC`, `hPos`,
`hErg`, `hIP`). They are hypotheses of the theorem, not axioms.

**How the challenge is organized.** The definitions are restated under their library names
(namespace `EinsteinRelation`) in the files under `Vocabulary/`: one file for each library
module that contains such a definition, with the declarations copied from that module in its
context (`namespace`, `open`, `variable`); lemmas that some definitions need are restated with
their proofs. Each vocabulary file imports only Mathlib and vocabulary files of this pair,
chosen so that it sees the same Mathlib modules as the library module it restates: Lean
resolves instances from the imported modules and shares auxiliary proofs within a file, so this
reproduces the library's definitions term for term. This file imports the vocabulary and the
Mathlib modules seen by `EinsteinRelation.MainTheorems`, and declares the theorem inside
`namespace EinsteinRelation.Frozen`, as the library does, so that every name resolves as there.
-/

section MobilityRate

open MeasureTheory

namespace EinsteinRelation.Frozen

theorem _root_.EinsteinRelationAudit.MobilityRate.mobility_rate
    (h45 : EinsteinRelation.External.AKM.ScalarStationaryEstimate)
    (h46 : EinsteinRelation.External.AKM.ScalarPlanarL2Estimate)
    (h47 : EinsteinRelation.External.AKM.ScalarHeatDifferenceEstimate)
    (h68 : EinsteinRelation.External.AKM.FluxGradientEstimate)
    (h614 : EinsteinRelation.External.AKM.FluxStationaryEstimate)
    (h615 : EinsteinRelation.External.AKM.FluxPlanarL2Estimate)
    (h616 : EinsteinRelation.External.AKM.FluxHeatDifferenceEstimate)
    (h832 : EinsteinRelation.External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : EinsteinRelation.External.GilbargTrudinger.InteriorRegularRepresentative)
    (hdecay : EinsteinRelation.External.AKM.ParabolicSemigroupKernelDecay)
    (hreg : EinsteinRelation.External.AKM.ParabolicLargeScale)
    (hEll : EinsteinRelation.External.AKM.EllipticLargeScale)
    (hE1 : EinsteinRelation.External.AKM.ParabolicHeatKernel)
    (hH2 : EinsteinRelation.External.AKM.CorrectorWeakH2)
    (hAKM : EinsteinRelation.AKMFluxDecayLargeTime)
    (hFOT : EinsteinRelation.FukushimaDecompositionInput)
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (hE : EinsteinRelation.GMPCouplingExistsV2Input)
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality)
    (hRV : EinsteinRelation.External.GMPReducedVelocityExistence)
    (hTC : EinsteinRelation.External.GMPTimeChangeLaw)
    (hPos : EinsteinRelation.External.GMPPhysicalVelocityPositive)
    (hErg : EinsteinRelation.External.GMPEnvironmentProcessErgodic)
    (hIP : EinsteinRelation.External.GMPReducedInvarianceAbar)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam := by
  sorry

end EinsteinRelation.Frozen

end MobilityRate
