import EinsteinRelation.Mobility.VelocityResolventRate

/-! # Proposition 5.3 on production carriers

Source: `paper/main.tex:895–906`. This conclusion uses the production expected
corrector flux and makes no reference to a frozen theorem or definition.
-/

open MeasureTheory
open scoped BigOperators
open EinsteinRelation.Correctors (reducedEnvironmentLaw reducedEnvironmentLaw_stationary
  canonicalCorrectorGradient)
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
open EinsteinRelation.Correctors.StationarySpatialRealization (spatialRealization)

namespace EinsteinRelation

/-- Proposition 5.3 on production carriers, conditional on the internal local-corrector
construction. Source: `paper/main.tex:895–906`. -/
theorem correctorLocal_of_construction (H53 : CorrectorLocalConstruction) :
  ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ),
    ∃ (phi : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → ℝ)
      (skew : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Mat d)
      (flux : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Vec d)
      (grad : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Vec d),
      (∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        (Measurable[reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => phi Q R i ω) ∧
            Measurable[reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => skew Q R i ω) ∧
            Measurable[reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => flux Q R i ω)) ∧
        (∀ ω, (skew Q R i ω).transpose = -(skew Q R i ω)) ∧
        HasWeakHorizontalGradient (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q) (phi Q R i) (grad Q R i) ∧
        (∀ j : Fin d,
          HasWeakHorizontalDivergence (reducedEnvironmentLaw Q)
            (reducedEnvironmentLaw_stationary Q)
            (fun (ω : FieldPair d) (k : Fin d) => skew Q R i ω j k)
            (fun ω : FieldPair d =>
              (∑ k, (ω.1 0) j k * (unitVector i k + grad Q R i ω k)) -
                (Correctors.expectedCorrectorFlux Q i).ofLp j -
                flux Q R i ω j))) ∧
      ∀ m : ℝ, 2 ≤ m → ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        (eLpNorm (phi Q R i) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) +
            eLpNorm (fun ω => EinsteinRelation.frobeniusNorm (skew Q R i ω)) (ENNReal.ofReal m)
              (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * EinsteinRelation.Correctors.correctorAmplitude d R)) ∧
        (eLpNorm (fun ω => euclideanNorm (flux Q R i ω)) (ENNReal.ofReal m)
              (reducedEnvironmentLaw Q) +
            eLpNorm (fun ω : FieldPair d =>
                euclideanNorm (fun j : Fin d =>
                  grad Q R i ω j -
                    (spatialRealization (canonicalCorrectorGradient Q i :
                        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                      ((0 : Vec d), ω)).ofLp j))
              (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * R⁻¹)) := by
  intro d hd Λ₀ r₀
  obtain ⟨phi, skew, flux, grad, hstruct, hbounds⟩ := H53 d (Fact.out : 2 ≤ d) Λ₀ r₀
  refine ⟨phi, skew, flux, grad, ?_, hbounds⟩
  intro Q R hR i
  obtain ⟨⟨hphi, hskew, hflux, _⟩, hanti, hgrad, hdiv⟩ := hstruct Q R hR i
  exact ⟨⟨hphi, hskew, hflux⟩, hanti, hgrad, hdiv⟩

end EinsteinRelation
