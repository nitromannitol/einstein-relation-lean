import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport

namespace EinsteinRelation.Frozen.Correctors

noncomputable def homogenizedCoefficientColumn
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  EinsteinRelation.Correctors.expectedCorrectorFlux Q i

end EinsteinRelation.Frozen.Correctors
