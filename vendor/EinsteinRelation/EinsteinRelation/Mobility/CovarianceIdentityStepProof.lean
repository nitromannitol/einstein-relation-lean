import EinsteinRelation.Mobility.MainSteps
import EinsteinRelation.Diffusion.GMPFamilyAPI
import EinsteinRelation.Diffusion.TimeChangeCovariance
import EinsteinRelation.External.GMPReducedInputs

/-! # Step 3 of Theorem 1.2: the covariance identity of the time change

Source: `paper/main.tex` 228-233. `CovarianceIdentityStep` follows from four cited inputs for the
GMP Section 7 families: existence of the reduced family, the time change between the physical and
reduced families, the clock rate of the unforced reduced family, and the annealed invariance
principle of the unforced reduced family with covariance `ā`. The analytic argument is
`TimeChangeCovariance.diffusivity_eq_of_timeChange`.
-/

open MeasureTheory

namespace EinsteinRelation

/-- `CovarianceIdentityStep` from the cited GMP inputs: for every physical GMP family, every
unforced diffusivity of the origin law is `(𝔼μ)⁻¹ ā`. -/
theorem covarianceIdentityStep_of_gmpInputs (hRF : External.GMPReducedFamilyExistence)
    (hTC : External.GMPTimeChangeLaw) (hErg : External.GMPEnvironmentProcessErgodic)
    (hIP : External.GMPReducedInvarianceAbar) : CovarianceIdentityStep := by
  intro d hd Λ₀ r₀ Q P hP cov hX
  obtain ⟨P', hP'⟩ := hRF d hd Λ₀ r₀ Q
  have hprob' : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω) :=
    isProbabilityMeasure_of_isGMPReducedOriginLaw hd Q.ellipticity_parameter Q 0 le_rfl
      zero_le_one (originLaw (P' 0)) (hP' 0 le_rfl zero_le_one)
  exact TimeChangeCovariance.diffusivity_eq_of_timeChange Q P P' hprob'
    (hTC d hd Λ₀ r₀ Q P P' hP hP' 0 le_rfl zero_le_one) (TimeChangeCovariance.meanClock_pos Q)
    (hErg d hd Λ₀ r₀ Q P' hP') (hIP d hd Λ₀ r₀ Q P' hP') hX

end EinsteinRelation
