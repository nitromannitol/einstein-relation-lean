import EinsteinRelation.Regeneration.OccupationFromGMPInputs
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Diffusion.Velocity
import EinsteinRelation.Mobility.MainTheoremFromPaperInputs

open MeasureTheory

namespace EinsteinRelation.Closure

/-- Theorem 1.2 (t.main, paper/main.tex:93-99): the diffusion is the GMP Section 7
process. Conditional on the cited inputs and the remaining internal results. -/
theorem mobilityRateV4_of_gmp_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (hE : GMPCouplingExistsV2Input) (hTail : GMPCouplingTailsV2Input)
    (hLoc : External.GMPKernelLocality)
    (hCons : Correctors.DecompositionConstruction)
    (H53 : CorrectorLocalConstruction) (H51 : CorrectorGradientMoments)
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
  have H32 := occupationStatement_of_inputs hE hTail hGir hInv hRF hLoc
  exact mobilityRate_of_paper_inputs' hFOT hGir hInv H32 hCons H53 H51 hAKM
    hRF hRV hTC hPos hErg hIP d hd Λ₀ r₀

end EinsteinRelation.Closure
