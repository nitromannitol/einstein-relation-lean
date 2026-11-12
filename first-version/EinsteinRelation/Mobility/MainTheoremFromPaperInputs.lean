import EinsteinRelation.Mobility.VelocityRateAssembly
import EinsteinRelation.Mobility.VelocityResolventRate
import EinsteinRelation.Mobility.VelocityAbelFromDecomposition
import EinsteinRelation.Mobility.DriftDecompositionFromSteps
import EinsteinRelation.Mobility.DriftBound
import EinsteinRelation.Mobility.QuenchedDriftFromFukushima
import EinsteinRelation.Mobility.AKMFluxDecaySplit
import EinsteinRelation.Mobility.CovarianceIdentityStepProof
import EinsteinRelation.Mobility.MainStepsBounds
import EinsteinRelation.Correctors.ScalarDecompositionGlue
import EinsteinRelation.Entropy.ResolventFromFisher
import EinsteinRelation.Entropy.FisherBoundAssembly

/-! # Theorem 1.2 from the remaining paper inputs

Source: `paper/main.tex`, Theorem 1.2 (lines 93-99) and its proof. `mobilityRate_of_paper_inputs`
has the conclusion of `mobilityRate_of_steps_noBounds` (the statement of the frozen Theorem 1.2,
`EinsteinRelation.mobility_rate`). Its hypotheses are paper results, proved elsewhere in this development, and the
cited inputs:

* `H41`: Lemma 4.1 (`FisherBoundStatement`);
* `H32`: Proposition 3.2 (`Entropy.OccupationStatement`);
* `hCons`: the construction of Proposition 6.1 (`Correctors.DecompositionConstruction`);
* `H53`: the local construction of Proposition 5.3 (`CorrectorLocalConstruction`);
* `H51`: the moments of Lemma 5.1 (`CorrectorGradientMoments`);
* the cited inputs `FukushimaDecompositionInput` (FOT Theorem 5.5.5), `AKMFluxDecayLargeTime`
  (AKM Theorem 4.1) and the GMP inputs of `EinsteinRelation.External`.

Lemmas 4.2 and 4.3 are derived (`Entropy.divergenceStatement_of_fisher_occupation`,
`Entropy.resolventStatement_of_fisher_occupation`), as are the velocity rate, the clock estimate
and the covariance identity.

`mobilityRate_of_paper_inputs'` also derives Lemma 4.1 (`Entropy.fisherBoundStatement_of_inputs`),
at the cost of the cited GMP Girsanov endpoint and unforced invariance inputs.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation

open EinsteinRelation.Carriers

/-- `OccupationStatement` in the form used by the Lemma 4.2 theorems: the coordinate-law input
`IQ` is specialized to `Q.measure`. -/
theorem occupation_universal_of_statement
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
      ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
        ∀ (P : QuenchedPathLaws d)
          (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
          IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
        ∀ G : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
          MemLp G (ENNReal.ofReal p) (reducedReferenceLaw Q) →
        ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
          (∫⁻ z : FieldPair d × Path d,
              (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal |G (reducedObservationAt t.toNNReal z)|)
            ∂(annealedCoordinateJoint Q.measure P origin_probability)) ≤
              ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q) ∧
          ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity Q.measure P origin_probability s rho →
            (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(reducedReferenceLaw Q)) ≤
              ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q) := by
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, H⟩ := H32 d hd Λ₀ r₀ hΛ hr
  refine ⟨l₀, hl₀, fun l hl => ?_⟩
  obtain ⟨p₀, hp₀, H'⟩ := H l hl
  refine ⟨p₀, hp₀, fun p hp => ?_⟩
  obtain ⟨C, hC, H''⟩ := H' p hp
  exact ⟨C, hC, fun Q lam hl0 hl1 P op hGMP => H'' Q lam hl0 hl1 Q.measure P op ⟨rfl, hGMP⟩⟩

/-- **Theorem 1.2** from the remaining paper inputs (Lemma 4.1, Proposition 3.2, the constructions
of Propositions 5.3 and 6.1, Lemma 5.1) and the cited inputs. -/
theorem mobilityRate_of_paper_inputs (hFOT : FukushimaDecompositionInput)
    (H41 : Correctors.FisherBoundStatement)
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀)
    (hCons : Correctors.DecompositionConstruction)
    (H53 : CorrectorLocalConstruction) (H51 : CorrectorGradientMoments)
    (hAKM : AKMFluxDecayLargeTime)
    (hRF : External.GMPReducedFamilyExistence) (hRV : External.GMPReducedVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hPos : External.GMPPhysicalVelocityPositive)
    (hErg : External.GMPEnvironmentProcessErgodic) (hIP : External.GMPReducedInvarianceAbar) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam := by
  have hOcc := occupation_universal_of_statement H32
  have H43 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.ResolventStatement d hd Λ₀ r₀ :=
    fun d hd Λ₀ r₀ => Entropy.resolventStatement_of_fisher_occupation hFOT d hd Λ₀ r₀ H41 hOcc
  have H61 : ScalarDecompositionTwin :=
    Correctors.scalarDecompositionTwin_of_construction H41 H43 H32 hCons
  have hFlux : AKMFluxDecay :=
    akmFluxDecay_of_largeTime hAKM (centredFluxMoments_of_correctorGradientMoments H51)
  have hRes : VelocityResolventRateStep :=
    velocityResolventRateStep_of_steps H53 H61 H43 H41 hFlux H51
  have hAbel : VelocityAbelStep := velocityAbelStep_of_driftDecomposition
    (driftDecompositionStep_of_steps driftBoundStep (quenchedDriftMartingaleStep_of_fukushima hFOT))
  have hV : VelocityRateStep := velocityRateStep_of_steps hAbel hRes
  have hC : ClockEstimateStep := Correctors.clockEstimateStep_of_construction H41 H43 H32 hCons
  have hS : CovarianceIdentityStep := covarianceIdentityStep_of_gmpInputs hRF hTC hErg hIP
  exact mobilityRate_of_steps_noBounds hV hC hS hRF hRV hTC hPos

/-- **Theorem 1.2** with Lemma 4.1 derived (`Entropy.fisherBoundStatement_of_inputs`). The
remaining paper inputs are Proposition 3.2, the constructions of Propositions 5.3 and 6.1, and
Lemma 5.1; the cited inputs add the GMP Girsanov endpoint and the unforced invariance. -/
theorem mobilityRate_of_paper_inputs' (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀)
    (hCons : Correctors.DecompositionConstruction)
    (H53 : CorrectorLocalConstruction) (H51 : CorrectorGradientMoments)
    (hAKM : AKMFluxDecayLargeTime)
    (hRF : External.GMPReducedFamilyExistence) (hRV : External.GMPReducedVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hPos : External.GMPPhysicalVelocityPositive)
    (hErg : External.GMPEnvironmentProcessErgodic) (hIP : External.GMPReducedInvarianceAbar) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam :=
  mobilityRate_of_paper_inputs hFOT (Entropy.fisherBoundStatement_of_inputs hFOT hGir hInv hRF)
    H32 hCons H53 H51 hAKM hRF hRV hTC hPos hErg hIP

end EinsteinRelation
