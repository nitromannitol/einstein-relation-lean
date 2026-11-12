import EinsteinRelation.Regeneration.OccupationFromGMPInputs
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Diffusion.Velocity
import EinsteinRelation.Environment.Smooth
import EinsteinRelation.Mobility.MainTheoremFromPaperInputs
import EinsteinRelation.Sharpness.SharpExampleFromInputs

open MeasureTheory Filter Topology

namespace EinsteinRelation.Closure

/-- Proposition 7.1 (sharp.example, paper/main.tex:1212-1219): the rate is attained;
the diffusion is the GMP Section 7 process. Conditional on the cited inputs and the construction of Proposition 6.1. -/
theorem sharpExampleV2_of_gmp_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (hE : GMPCouplingExistsV2Input) (hTail : GMPCouplingTailsV2Input)
    (hLoc : External.GMPKernelLocality)
    (hCons : Correctors.DecompositionConstruction)
    (hRV : External.GMPReducedVelocityExistence) (hPF : External.GMPPhysicalFamilyExistence)
    (hVX : External.GMPVelocityExistence) (hTC : External.GMPTimeChangeLaw)
    (hErg : External.GMPEnvironmentProcessErgodic) (hIP : External.GMPReducedInvarianceAbar)
    (hPos : External.GMPPhysicalVelocityPositive)
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
  have H32 := occupationStatement_of_inputs hE hTail hGir hInv hRF hLoc
  have H41 := Entropy.fisherBoundStatement_of_inputs hFOT hGir hInv hRF
  have hOcc := occupation_universal_of_statement H32
  have H43 := fun d hd Λ₀ r₀ =>
    Entropy.resolventStatement_of_fisher_occupation hFOT d hd Λ₀ r₀ H41 hOcc
  have H61 := Correctors.scalarDecompositionTwin_of_construction H41 H43 H32 hCons
  exact Sharpness.sharpExample_of_scalarDecomposition d hd hW hFOT H61
    hRF hRV hPF hVX hTC hErg hIP hPos

end EinsteinRelation.Closure
