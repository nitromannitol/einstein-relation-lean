import EinsteinRelation.Correctors.AKMCanonicalMollifierMoments
import EinsteinRelation.Correctors.CanonicalShiftedMeansFromMoments

/-! # Planar canonical shifted means from AKM (4.126)

Source: `paper/main.tex:948–955`. The actual canonical gradient and centered
flux convolution bounds give the printed scalar and skew-column shifted means.
The source corrector, its canonical identification, and the scalar/skew weak
equations are explicit internal obligations of the source construction.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The same law-independent constant controls every actual canonical scalar
potential and every column of its associated planar skew potential, independently
of their additive constants. Source: `paper/main.tex:948–955`. -/
theorem correctorWeakH2_canonical_planar_shifted_means (hAKM : CorrectorWeakH2)
    (L r₀ m : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
      (φ : Coefficient 2 (AKMUpperEllipticity L) → Vec 2 → ℝ)
      (G : Coefficient 2 (AKMUpperEllipticity L) → Vec 2 → Vec 2),
      IsFirstOrderCorrector (actualCoefficientLaw Q) (halfDirection i) φ G →
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec 2)),
        (2 : ℝ) • (halfDirection i + G (project (r₀ := r₀) Q.ellipticity_parameter ω) x) =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • x) (reduce ω.1))).ofLp) →
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
  obtain ⟨C, hC, hbound⟩ := correctorWeakH2_canonical_gradient_flux_moments
    hAKM L r₀ m hL hr₀ (zero_lt_one.trans_le hm)
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q i φ G hc hid u S hu hS hdiv R hR y hy
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hg := canonical_scalar_shift_moment_le_of_coordinate_bounds
    (by norm_num : 0 < 2) Q i hm hC.le hR0 u hu
    (fun x hx j => (le_add_right le_rfl).trans (hbound Q i φ G hc hid R hR x hx j)) y hy
  have hq (k : Fin 2) := canonical_planar_skew_column_shift_moment_le_of_coordinate_bounds
    Q i hm hC.le hR0 S hS hdiv
    (fun x hx j => (le_add_left le_rfl).trans (hbound Q i φ G hc hid R hR x hx j)) y hy k
  exact ⟨hg, hq⟩

end EinsteinRelation.Correctors
