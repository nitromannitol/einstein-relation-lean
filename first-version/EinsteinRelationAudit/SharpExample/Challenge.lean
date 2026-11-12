import Mathlib
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.Generator
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.HorizontalSobolev
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.HorizontalTranslationLp
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.Weak
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.WeightedH1QuotientSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Carriers.DensityAnnealedTwins
import EinsteinRelationAudit.SharpExample.Vocabulary.Carriers.RegenerationCorrectorTwins
import EinsteinRelationAudit.SharpExample.Vocabulary.Clock.PhysicalClock
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.EllipticOperatorBound
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.EuclideanCoordinateCharacterization
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.EuclideanCoordinateMoments
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.EuclideanLpCoordinateAssembly
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.HeatSmoothing
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.HorizontalH1EuclideanGradient
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.StationaryGradientDomainSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.ClockInverseSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.GMPFamily
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.AKMTestIntegralSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Bounds
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.CoefficientRestriction
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.MatrixNorm
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Reduction
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Smooth
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.SourceReducedBoundSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.External.AKMCorrectorOscillation
import EinsteinRelationAudit.SharpExample.Vocabulary.External.AKMEnergyDensity
import EinsteinRelationAudit.SharpExample.Vocabulary.External.AKMHeatKernel
import EinsteinRelationAudit.SharpExample.Vocabulary.External.AKMKernelSemigroup
import EinsteinRelationAudit.SharpExample.Vocabulary.External.AKMLocalCorrectors
import EinsteinRelationAudit.SharpExample.Vocabulary.External.GMPLocalityInput
import EinsteinRelationAudit.SharpExample.Vocabulary.External.GMPPhysicalInputs
import EinsteinRelationAudit.SharpExample.Vocabulary.External.GMPReducedInputs
import EinsteinRelationAudit.SharpExample.Vocabulary.External.GantertSection7Support
import EinsteinRelationAudit.SharpExample.Vocabulary.External.GilbargTrudinger
import EinsteinRelationAudit.SharpExample.Vocabulary.External.WhiteNoise
import EinsteinRelationAudit.SharpExample.Vocabulary.Mobility.QuenchedDriftFromFukushima
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.LocalSigma
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ProbabilityPart
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ReductionLocality
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ValidAnnealedLawSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.Construction
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.Coupling
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.FirstRewardSteps
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.OccupationLaterIntervals
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.RenewalCarriers
import EinsteinRelationAudit.SharpExample.Vocabulary.Sharpness.NoiseKernel

/-!
# Proposition 7.1 (paper label `sharp.example`): Mathlib-only statement

This file states Proposition 7.1 of *Quantitative Einstein relation for reversible diffusions in
a random environment* (Ahmed Bou-Rabee and Ruizhe Xu), which shows that the rate of Theorem 1.2 is
attained, together with every definition that the statement uses. The challenge imports only Mathlib
(directly and through its `Vocabulary/` files). The final theorem has the one intentional
`sorry` of the challenge; `Solution.lean` proves the same
theorem from the library, and the comparator checks that the two statements, and all the
definitions they depend on, are identical.

**The statement.** Assume the 29 literature inputs `h45`, …, `hW` (see below). For every `d ≥ 2`
there are constants `Λ₀, r₀`, an environment law `Q` satisfying Assumption 1.1 with these
constants (`EnvironmentLaw d Λ₀ r₀`) whose fields are almost surely smooth
(`IsSmoothFieldPair`), and `c > 0`, such that, for every family `P` of quenched path laws that is
the diffusion of Gantert, Mathieu and Piatnitski (2012, Section 7) for `Q`
(`IsGMPPhysicalFamily`), every diffusivity `Σ_X` of the unforced diffusion (`HasDiffusivity`) and
every function `λ ↦ ℓ(λ)` such that `ℓ(λ)` is the quenched velocity for every `λ ∈ (0, 1]`
(`HasQuenchedVelocity`), the ratio `((λ⁻¹ ℓ(λ) − Σ_X e₁) · e₁) / λ` tends to `c` as `λ ↓ 0`.

**The hypotheses.** The literature inputs are Prop-valued definitions, restated below with the
docstrings that record their sources: Armstrong, Kuusi and Mourrat (2019) (`h45`, `h46`, `h47`,
`h68`, `h614`, `h615`, `h616`, `hdecay`, `hreg`, `hEll`, `hE1`, `hH2`, and the existence of white
noise `hW`, stated for every `d ≥ 2`), Gilbarg and Trudinger (2001) (`h832`, `h836`), Fukushima,
Oshima and Takeda (2011) (`hFOT`), and Gantert, Mathieu and Piatnitski (2012) (`hGir`, `hInv`,
`hRF`, `hE`, `hTail`, `hLoc`, `hRV`, `hTC`, `hPos`, `hErg`, `hIP`, `hPF`, `hVX`). They are
hypotheses of the theorem, not axioms.

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

section MobilityRateSharp

open MeasureTheory Filter Topology

namespace EinsteinRelation.Frozen

theorem _root_.EinsteinRelationAudit.SharpExample.mobility_rate_sharp
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
    (hPF : EinsteinRelation.External.GMPPhysicalFamilyExistence)
    (hVX : EinsteinRelation.External.GMPVelocityExistence)
    (hW : ∀ d : ℕ, 2 ≤ d → EinsteinRelation.External.WhiteNoiseExistence d)
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    (∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (P : DiffusionFamily d), IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
    ∀ (velocity : ℝ → Vec d),
      (∀ lam : ℝ, 0 < lam → lam ≤ 1 →
        HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
      Tendsto (fun lam : ℝ =>
          dot ((lam⁻¹ • velocity lam) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
            (unitVector (⟨0, by omega⟩ : Fin d)) / lam)
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  sorry

end EinsteinRelation.Frozen

end MobilityRateSharp
