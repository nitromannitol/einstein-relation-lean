import EinsteinRelation.Calculus.SourceMollifierSupport
import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport

open MeasureTheory

namespace EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport

open NormalizedSpatialRepresentativeSupport
open StationarySpatialRealization

def IsNormalizedCanonicalScalarCorrector
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (φ : FieldPair d → Point d → ℝ) : Prop :=
  Measurable (fun p : Vec d × FieldPair d =>
    φ p.2 (WithLp.toLp 2 p.1)) ∧
  ∀ᵐ ω ∂reducedEnvironmentLaw Q,
    ∃ hLI : LocallyIntegrable (fun x : Point d => φ ω x) volume,
      let ψ : ScalarSpatialPotential d := ⟨φ ω, hLI⟩
      HasWeakGradient Set.univ
        (fun x : Vec d => φ ω (WithLp.toLp 2 x))
        (fun x : Vec d =>
          (spatialRealization
            (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (x, ω)).ofLp) ∧
      sourceMollifierNormalize ζ R hR y
        (Quotient.mk (spatialGaugeSetoid d ℝ) ψ) =
      Quotient.mk (spatialAESetoid d ℝ) ψ

def IsNormalizedPhysicalScalarPullback
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (φ : FieldPair d → Point d → ℝ) : Prop :=
  Measurable (fun p : Vec d × FieldPair d =>
    φ (reduce p.2) (WithLp.toLp 2 p.1)) ∧
  ∀ᵐ ω ∂Q.measure,
    ∃ hLI : LocallyIntegrable (fun x : Point d => φ (reduce ω) x) volume,
      let ψ : ScalarSpatialPotential d := ⟨fun x : Point d => φ (reduce ω) x, hLI⟩
      HasWeakGradient Set.univ
        (fun x : Vec d => φ (reduce ω) (WithLp.toLp 2 x))
        (fun x : Vec d =>
          (spatialRealization
            (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (x, reduce ω)).ofLp) ∧
      sourceMollifierNormalize ζ R hR y
        (Quotient.mk (spatialGaugeSetoid d ℝ) ψ) =
      Quotient.mk (spatialAESetoid d ℝ) ψ

theorem normalizedPhysicalScalarPullback_of_reduced
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (φ : FieldPair d → Point d → ℝ)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ) :
    IsNormalizedPhysicalScalarPullback Q i ζ R hR y φ := by
  have hmap : Measure.QuasiMeasurePreserving reduce Q.measure (reducedEnvironmentLaw Q) := by
    change Measure.QuasiMeasurePreserving reduce Q.measure (Measure.map reduce Q.measure)
    exact Probability.measurable_reduce.quasiMeasurePreserving Q.measure
  refine ⟨?_, ?_⟩
  · exact hφ.1.comp (measurable_fst.prodMk
      (Probability.measurable_reduce.comp measurable_snd))
  · exact hmap.ae hφ.2

theorem normalizedPhysicalScalarPullback_weakGradient_and_normalization
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (φ : FieldPair d → Point d → ℝ)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ) :
    ∀ᵐ ω ∂Q.measure,
      ∃ hLI : LocallyIntegrable (fun x : Point d => φ (reduce ω) x) volume,
        let ψ : ScalarSpatialPotential d :=
          ⟨fun x : Point d => φ (reduce ω) x, hLI⟩
        HasWeakGradient Set.univ
          (fun x : Vec d => φ (reduce ω) (WithLp.toLp 2 x))
          (fun x : Vec d =>
            (spatialRealization
              (canonicalCorrectorGradient Q i :
                Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (x, reduce ω)).ofLp) ∧
        sourceMollifierNormalize ζ R hR y
          (Quotient.mk (spatialGaugeSetoid d ℝ) ψ) =
        Quotient.mk (spatialAESetoid d ℝ) ψ :=
  (normalizedPhysicalScalarPullback_of_reduced Q i ζ R hR y φ hφ).2

end EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport
