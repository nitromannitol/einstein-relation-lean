import EinsteinRelation.Closure.MainRateFromGMPInputs
import EinsteinRelation.Closure.SharpExampleFromGMPInputs
import EinsteinRelation.Closure.ScalarDecompositionV2Twin
import EinsteinRelation.Correctors.DecompositionConstructionFromInputs
import EinsteinRelation.Regeneration.OccupationFromGMPInputs
import EinsteinRelation.Mobility.AKMFluxDecaySplit
import EinsteinRelation.Mobility.VelocityResolventRate

/-! # Conditional closures from the corrector inputs

The conditional closures of Theorem 1.2, Proposition 7.1 and
Proposition 6.1 (over the production twins) take the decomposition construction
`Correctors.DecompositionConstruction` as a premise. Here that premise is replaced by its two
sources: the first assertion of Lemma 5.1 (`CorrectorGradientMoments`) and the localized corrector
construction of Proposition 5.3 (`CorrectorLocalConstruction`). The construction is obtained from
them by `Correctors.decompositionConstruction_of_inputs`.

The remaining premises are the cited inputs and the GMP inputs. The occupation statement of
Proposition 3.2 is obtained from the GMP inputs by `occupationStatement_of_inputs`.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Closure

/-- Theorem 1.2 (t.main, paper/main.tex:93-99): the diffusion is the GMP Section 7
process. Conditional on the cited inputs and the two corrector inputs `H51` and `H53`. -/
theorem mobilityRateV4_of_corrector_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (hE : GMPCouplingExistsV2Input) (hTail : GMPCouplingTailsV2Input)
    (hLoc : External.GMPKernelLocality)
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
        ≤ C * lam :=
  mobilityRateV4_of_gmp_inputs hFOT hGir hInv hRF hE hTail hLoc
    (Correctors.decompositionConstruction_of_inputs H51 H53) H53 H51 hAKM hRV hTC hPos hErg hIP
    d hd Λ₀ r₀

/-- Proposition 7.1 (sharp.example, paper/main.tex:1212-1219): the rate is attained;
the diffusion is the GMP Section 7 process. Conditional on the cited inputs and the two corrector
inputs `H53` and `H51`, which give the construction of Proposition 6.1. -/
theorem sharpExampleV2_of_corrector_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (hE : GMPCouplingExistsV2Input) (hTail : GMPCouplingTailsV2Input)
    (hLoc : External.GMPKernelLocality)
    (H53 : CorrectorLocalConstruction) (H51 : CorrectorGradientMoments)
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
        (𝓝[>] (0 : ℝ)) (𝓝 c) :=
  sharpExampleV2_of_gmp_inputs hFOT hGir hInv hRF hE hTail hLoc
    (Correctors.decompositionConstruction_of_inputs H51 H53) hRV hPF hVX hTC hErg hIP hPos
    d hd hW

/-- Proposition 6.1 (scalar.decomposition, `paper/main.tex` 978-997), over the
production twins. Conditional on the cited inputs, the GMP coupling and locality inputs that give
the occupation statement of Proposition 3.2, and the two corrector inputs `H53` and `H51`. -/
theorem scalarDecompositionV2Twin_of_gmp_corrector_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (hE : GMPCouplingExistsV2Input) (hTail : GMPCouplingTailsV2Input)
    (hLoc : External.GMPKernelLocality)
    (H53 : CorrectorLocalConstruction) (H51 : CorrectorGradientMoments) :
    ScalarDecompositionTwin :=
  scalarDecompositionV2Twin_of_inputs hFOT hGir hInv hRF
    (occupationStatement_of_inputs hE hTail hGir hInv hRF hLoc)
    (Correctors.decompositionConstruction_of_inputs H51 H53)

end EinsteinRelation.Closure
