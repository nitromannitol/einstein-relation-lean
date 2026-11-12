import EinsteinRelation.Correctors.AKMPlanarCanonicalShiftedMeans
import EinsteinRelation.Correctors.AKMGlobalCorrectorConstruction
import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationSublinearity

/-! # Canonical planar moments from the existing literature inputs

Source: `paper/main.tex:789–810,948–955`. The raw source corrector and its
global identification are constructed from the existing ball Poincare input.
Consequently the AKM coordinate and shifted-mean estimates need no separate
source-existence or identification hypotheses.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Canonical gradient and centered-flux mollifier moments follow from the
existing AKM and Poincare inputs. Source: `paper/main.tex:948–955`. -/
theorem canonical_planar_mollifier_moments_of_literature (hAKM : CorrectorWeakH2)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (L r₀ m : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2),
      ∀ R : ℝ, 1 ≤ R → ∀ y : Vec 2, euclideanNorm y ≤ R → ∀ j : Fin 2,
        eLpNorm (fun ω => ((fun x => ((canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp j)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Calculus.unitMassScaledMollifier 2 R) y)
          (ENNReal.ofReal m) (reducedEnvironmentLaw Q) +
        eLpNorm (fun ω => ((fun x => ((canonicalCorrectorFlux Q i (translate x ω)).ofLp -
            (expectedCorrectorFlux Q i).ofLp) j)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Calculus.unitMassScaledMollifier 2 R) y)
          (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹) := by
  obtain ⟨C, hC, hbound⟩ := correctorWeakH2_canonical_gradient_flux_moments
    hAKM L r₀ m hL hr₀ hm
  letI : Fact (2 ≤ 2) := ⟨le_rfl⟩
  refine ⟨C, hC, ?_⟩
  intro Q i
  obtain ⟨φ, hid⟩ := exists_akmCorrector_global_gradient_identification hP Q i
  exact hbound Q i φ.potential φ.grad (EinsteinRelation.Correctors.Corrector.isFirstOrderCorrector φ) hid

/-- Literal shifted means of any actual canonical scalar and planar skew
potential satisfy the same uniform bound. Source: `paper/main.tex:948–955`. -/
theorem canonical_planar_shifted_means_of_literature (hAKM : CorrectorWeakH2)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (L r₀ m : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2),
      ∀ (u : FieldPair 2 → Vec 2 → ℝ) (S : FieldPair 2 → Vec 2 → Mat 2),
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakGradient Set.univ (u ω)
        (fun x => ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q)) (translate x ω)).ofLp)) →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂volume, (S ω x).transpose = -(S ω x)) →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakRowDivergence Set.univ (S ω)
        (fun x => (canonicalCorrectorFlux Q i (translate x ω)).ofLp -
          (expectedCorrectorFlux Q i).ofLp)) →
      ∀ R : ℝ, 1 ≤ R → ∀ y : Vec 2, euclideanNorm y ≤ R →
        (MemLp (fun ω => ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
            Calculus.unitMassScaledMollifier 2 R (z - y)) * u ω z)
            (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ∧
          eLpNorm (fun ω => ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
            Calculus.unitMassScaledMollifier 2 R (z - y)) * u ω z)
            (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C) ∧
        ∀ k : Fin 2,
          MemLp (fun ω => euclideanNorm (fun j => ∫ z,
            (Calculus.unitMassScaledMollifier 2 R z -
              Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z j k))
              (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ∧
          eLpNorm (fun ω => euclideanNorm (fun j => ∫ z,
            (Calculus.unitMassScaledMollifier 2 R z -
              Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z j k))
              (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hbound⟩ := correctorWeakH2_canonical_planar_shifted_means
    hAKM L r₀ m hL hr₀ hm
  letI : Fact (2 ≤ 2) := ⟨le_rfl⟩
  refine ⟨C, hC, ?_⟩
  intro Q i
  obtain ⟨φ, hid⟩ := exists_akmCorrector_global_gradient_identification hP Q i
  exact hbound Q i φ.potential φ.grad (EinsteinRelation.Correctors.Corrector.isFirstOrderCorrector φ) hid

end EinsteinRelation.Correctors
