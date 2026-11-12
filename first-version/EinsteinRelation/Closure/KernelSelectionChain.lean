import EinsteinRelation.Closure.EndToEnd
import EinsteinRelation.Correctors.CorrectorLocalFromMeasurableKernel
import EinsteinRelation.Correctors.ConditionalFromGradientCopies
import EinsteinRelation.Mobility.CorrectorLocalFromConstruction

/-! # The final corrector, decomposition, sharpness and mobility chain

Source: `paper/main.tex:93–99,766–776,887–989,1204–1211`.
The cited inputs are explicit hypotheses. The only additional internal
obligation is coefficient-joint measurable selection of the scalar E.1
kernel. In particular, the continuous-representative conditional estimate
is the successor form of Lemma 5.2.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Closure

open Correctors External.AKM External.GilbargTrudinger
open Environment.AKMTestIntegralSupport ReductionImageV3
open Correctors.NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance kernelChainRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

variable
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (hEll : EllipticLargeScale)
    (hkernel : ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ (CK : ℝ → ℝ)
        (P : Coefficient d (AKMUpperEllipticity L) → ℝ → Vec d → Vec d → ℝ),
        (∀ α, 0 < α → α < (AKMUpperEllipticity L)⁻¹ → 0 < CK α) ∧
        Measurable (fun z :
          (Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d)) × Vec d =>
          P z.1.1 z.1.2.1 z.1.2.2 z.2) ∧
        ∀ᵐ A ∂actualCoefficientLaw Q,
          ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
            (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A (P A) X Y H CK)

include h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 hdecay hreg hEll hkernel

/-- Lemma 5.2 with continuous scalar and skew representatives. All paired
estimates are supplied by the actual point-copy decay; no corrector bound
is assumed. Source: `paper/main.tex:766–776,826–886`. -/
theorem correctorConditional_finalChain : CorrectorConditionalContinuousStatement := by
  apply correctorConditionalContinuous_of_literature_and_gradient_copy_bounds
    h45 h46 h68 h614 h615 hP h817 h832 h836
  intro d hd L r₀ m hm
  have H51 := correctorGradientMoments_of_frozen_inputs
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
  obtain ⟨C, hC⟩ := gradient_copy_decay_of_measurable_kernel
    hdecay hreg hEll hP h817 h832 h836 H51 d L r₀ m hm (hkernel d L r₀)
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro Q R hR y i
  exact (hC Q R hR y i).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)))

variable (hH2 : CorrectorWeakH2)
include hH2

/-- Proposition 5.3's production construction from cited inputs and a
coefficient-joint measurable scalar kernel. The source families and their
continuity, normalization, moments and locality are proved internally.
Source: `paper/main.tex:887–969`. -/
theorem correctorLocalConstruction_finalChain : CorrectorLocalConstruction := by
  exact correctorLocalConstruction_of_measurable_kernel hP h836
    hdecay hreg hEll h45 h46 h47 h68 h614 h615 h616 h817 h832 hH2 hkernel

variable
    (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (hE : GMPCouplingExistsV2Input) (hTail : GMPCouplingTailsV2Input)
    (hLoc : External.GMPKernelLocality)

include hFOT hGir hInv hRF hE hTail hLoc

/-- Proposition 6.1 over the production carriers, from the local corrector
construction and the proved gradient part of Lemma 5.1. The cited GMP
inputs also supply Proposition 3.2. Source: `paper/main.tex:970–989`. -/
theorem scalarDecomposition_finalChain : ScalarDecompositionTwin := by
  have H53 := correctorLocalConstruction_finalChain
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 hdecay hreg hEll hkernel hH2
  have H51 := correctorGradientMoments_of_frozen_inputs
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
  exact scalarDecompositionV2Twin_of_gmp_corrector_inputs
    hFOT hGir hInv hRF hE hTail hLoc H53 H51

/-- Theorem 1.2 for the GMP physical diffusion family, with constants before
the environment law and family. The only internal hypothesis beyond the
cited inputs is measurable kernel selection. Source: `paper/main.tex:93–99`. -/
theorem mobilityRate_finalChain
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
        ≤ C * lam := by
  have H53 := correctorLocalConstruction_finalChain
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 hdecay hreg hEll hkernel hH2
  have H51 := correctorGradientMoments_of_frozen_inputs
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
  exact mobilityRateV4_of_corrector_inputs hFOT hGir hInv hRF hE hTail hLoc
    H53 H51 hAKM hRV hTC hPos hErg hIP d hd Λ₀ r₀

/-- Proposition 7.1: the positive sharpness limit for the GMP physical
diffusion family, with the same corrector construction. The white-noise
existence hypothesis is the existing cited input for the example.
Source: `paper/main.tex:1204–1211`. -/
theorem sharpExample_finalChain
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
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  have H53 := correctorLocalConstruction_finalChain
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 hdecay hreg hEll hkernel hH2
  have H51 := correctorGradientMoments_of_frozen_inputs
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
  exact sharpExampleV2_of_corrector_inputs hFOT hGir hInv hRF hE hTail hLoc
    H53 H51 hRV hPF hVX hTC hErg hIP hPos d hd hW

end EinsteinRelation.Closure
