import EinsteinRelation.Closure.KernelSelectionChain
import EinsteinRelation.Correctors.KernelGraphClosed

/-! # The final chain from the cited inputs alone

Source: `paper/main.tex:93–99,766–776,887–989,1204–1211`. The single
internal premise `hkernel` of `KernelSelectionChain` (coefficient-joint
measurable selection of the scalar E.1 kernel) is proved from the cited
AKM Proposition E.1 (`ParabolicHeatKernel`) by the closed-graph argument
of `Correctors/KernelGraphClosed.lean`. Lemma 5.2 (continuous
successor form), Proposition 5.3, Proposition 6.1, Theorem 1.2 and
Proposition 7.1 then follow from the listed cited inputs only.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Closure

open Correctors External.AKM External.GilbargTrudinger
open Environment.AKMTestIntegralSupport ReductionImageV3
open Correctors.NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance citedInputsRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

variable
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (hEll : EllipticLargeScale) (hE1 : ParabolicHeatKernel)

include h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 hdecay hreg hEll hE1

/-- Lemma 5.2 with continuous scalar and skew representatives
(`corrector.conditional`), from the cited inputs alone.
Source: `paper/main.tex:766–776,826–886`. -/
theorem correctorConditional_of_cited_inputs :
    CorrectorConditionalContinuousStatement :=
  correctorConditional_finalChain h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
    hdecay hreg hEll (BorelKernel.measurableKernelHypothesis_of_parabolicHeatKernel hE1)

variable (hH2 : CorrectorWeakH2)
include hH2

/-- Proposition 5.3's production construction from the cited inputs alone.
Source: `paper/main.tex:887–969`. -/
theorem correctorLocalConstruction_of_cited_inputs : CorrectorLocalConstruction :=
  correctorLocalConstruction_finalChain h45 h46 h47 h68 h614 h615 h616 hP h817 h832
    h836 hdecay hreg hEll (BorelKernel.measurableKernelHypothesis_of_parabolicHeatKernel hE1)
    hH2

variable
    (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (hE : GMPCouplingExistsV2Input) (hTail : GMPCouplingTailsV2Input)
    (hLoc : External.GMPKernelLocality)

include hFOT hGir hInv hRF hE hTail hLoc

/-- Proposition 6.1 over the production carriers, from the cited inputs
alone. Source: `paper/main.tex:970–989`. -/
theorem scalarDecomposition_of_cited_inputs : ScalarDecompositionTwin :=
  scalarDecomposition_finalChain h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
    hdecay hreg hEll (BorelKernel.measurableKernelHypothesis_of_parabolicHeatKernel hE1)
    hH2 hFOT hGir hInv hRF hE hTail hLoc

/-- Theorem 1.2 for the GMP physical diffusion family, from the cited
inputs alone, with constants before the environment law and family.
Source: `paper/main.tex:93–99`. -/
theorem mobilityRate_of_cited_inputs
    (hAKM : AKMFluxDecayLargeTime) (hRV : External.GMPReducedVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hPos : External.GMPPhysicalVelocityPositive)
    (hErg : External.GMPEnvironmentProcessErgodic) (hIP : External.GMPReducedInvarianceAbar)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam :=
  mobilityRate_finalChain h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
    hdecay hreg hEll (BorelKernel.measurableKernelHypothesis_of_parabolicHeatKernel hE1)
    hH2 hFOT hGir hInv hRF hE hTail hLoc hAKM hRV hTC hPos hErg hIP d hd Λ₀ r₀

/-- Proposition 7.1: the positive sharpness limit for the GMP physical
diffusion family, from the cited inputs alone.
Source: `paper/main.tex:1204–1211`. -/
theorem sharpExample_of_cited_inputs
    (hRV : External.GMPReducedVelocityExistence)
    (hPF : External.GMPPhysicalFamilyExistence) (hVX : External.GMPVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hErg : External.GMPEnvironmentProcessErgodic)
    (hIP : External.GMPReducedInvarianceAbar) (hPos : External.GMPPhysicalVelocityPositive)
    (d : ℕ) (hd : 2 ≤ d) (hW : External.WhiteNoiseExistence d) :
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
        (𝓝[>] (0 : ℝ)) (𝓝 c) :=
  sharpExample_finalChain h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
    hdecay hreg hEll (BorelKernel.measurableKernelHypothesis_of_parabolicHeatKernel hE1)
    hH2 hFOT hGir hInv hRF hE hTail hLoc hRV hPF hVX hTC hErg hIP hPos d hd hW

end EinsteinRelation.Closure
