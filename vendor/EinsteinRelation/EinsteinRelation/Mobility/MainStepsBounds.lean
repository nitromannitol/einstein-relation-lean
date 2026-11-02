import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import EinsteinRelation.Mobility.MainTheoremFromSteps

/-! # The a-priori bounds of Theorem 1.2

Source: `paper/main.tex`, Theorem 1.2 (`t.main`, lines 93-99) and its proof (lines 1187-1199).
`mobilityRate_of_steps` takes the ranges of `ā e₁` and of the mean clock as the hypothesis
`hBounds`. This module proves those ranges with the constant `Λ = sourceReducedBound Λ₀`, from
the column bound `|ā e₁| ≤ Λ` and the clock-mean bounds `Λ⁻¹ ≤ 𝔼μ ≤ Λ` of
`Correctors.HomogenizedMatrixBounds`. The result is `mobilityRate_of_steps_noBounds`, the
statement of Theorem 1.2 with the three internal steps and the cited GMP inputs as its only
hypotheses.
-/

open MeasureTheory
open EinsteinRelation.Correctors

namespace EinsteinRelation

/-- The matrix `ā` of `MainSteps` is the homogenized matrix of `HomogenizedMatrixBounds`: both
have `i`-th column the expected corrector flux `E[a(e_i + ∇φ_i)]`. -/
theorem abar_eq_homogenizedMatrix {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    abar Q = homogenizedMatrix Q := by
  ext j i
  rfl

/-- The mean clock density `𝔼μ` is the mean of the second coordinate under the reduced law. -/
theorem meanMu_eq_reducedClockMean {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    meanMu Q = ∫ ω, ω.2 (0 : Vec d) ∂(reducedEnvironmentLaw Q) := by
  have hcont : Continuous (fun ω : FieldPair d => ω.2 (0 : Vec d)) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_snd
  have hred : ∫ ω, ω.2 (0 : Vec d) ∂(reducedEnvironmentLaw Q) =
      ∫ ω, clockDensity ω 0 ∂Q.measure := by
    rw [reducedEnvironmentLaw]
    exact integral_map Probability.measurable_reduce.aemeasurable
      hcont.aestronglyMeasurable
  exact hred.symm

/-- The a-priori ranges of Theorem 1.2: the column `ā e₁` has Euclidean norm at most
`Λ = sourceReducedBound Λ₀`, and the mean clock `𝔼μ` lies in `[Λ⁻¹, Λ]`. -/
theorem mainSteps_bounds (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) :
    euclideanNorm (abarE1 hd Q) ≤ sourceReducedBound Λ₀ ∧
      (sourceReducedBound Λ₀)⁻¹ ≤ meanMu Q ∧ meanMu Q ≤ sourceReducedBound Λ₀ := by
  have hA : abarE1 hd Q = (homogenizedMatrix Q).mulVec (unitVector (⟨0, by omega⟩ : Fin d)) := by
    rw [← abar_mulVec_unitVector_zero hd Q, abar_eq_homogenizedMatrix Q]
  obtain ⟨hlo, hhi⟩ := reducedClockMean_bounds Q
  rw [← meanMu_eq_reducedClockMean Q] at hlo hhi
  refine ⟨?_, hlo, hhi⟩
  rw [hA]
  exact homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q _

/-- Theorem 1.2 from the internal steps and the cited GMP inputs. This is the statement of
`mobilityRate_of_steps` without the hypothesis `hBounds`, which `mainSteps_bounds` supplies. -/
theorem mobilityRate_of_steps_noBounds (hV : VelocityRateStep) (hC : ClockEstimateStep)
    (hS : CovarianceIdentityStep)
    (hRF : External.GMPReducedFamilyExistence) (hRV : External.GMPReducedVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hPos : External.GMPPhysicalVelocityPositive) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam :=
  mobilityRate_of_steps hV hC hS hRF hRV hTC hPos mainSteps_bounds

end EinsteinRelation
