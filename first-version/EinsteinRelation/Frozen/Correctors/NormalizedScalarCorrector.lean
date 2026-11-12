import EinsteinRelation.Calculus.SourceMollifierSupport
import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport

open MeasureTheory

namespace EinsteinRelation.Correctors.NormalizedScalarCorrectorMeaning

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

end EinsteinRelation.Correctors.NormalizedScalarCorrectorMeaning
