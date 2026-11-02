import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `corrector-construction`, `paper/main.tex:794`.
The gradient is the actual frozen variational corrector, uniquely determined
in the closed mean-zero horizontal potential space. The matrix is its actual
expected flux, and its ellipticity constant precedes the law. Dimension two
requires only this gradient, not a stationary scalar potential. -/
def node_corrector_u2D_constructionStmt : Prop :=
  ∀ Λ₀ : ℝ, 1 ≤ Λ₀ → ∃ Λ : ℝ, 1 ≤ Λ ∧
    ∀ (d : ℕ), 2 ≤ d → ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
      IsElliptic Λ (fun _ : Vec d => homogenizedCoefficient Q) ∧
      ∀ i : Fin d, ∃ G : Correctors.correctorPotentialDomain Q,
        (G.val : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) = correctorGradient Q i ∧
        (∀ f : horizontalH1 (Correctors.reducedEnvironmentLaw Q)
            (Correctors.reducedEnvironmentLaw_stationary Q),
          inner ℝ (Correctors.horizontalEuclideanGradient (Correctors.reducedEnvironmentLaw Q)
            (Correctors.reducedEnvironmentLaw_stationary Q) f)
            (Correctors.correctorFluxOfGradient Q i G) = 0) ∧
        (∀ G' : Correctors.correctorPotentialDomain Q,
          (∀ f : horizontalH1 (Correctors.reducedEnvironmentLaw Q)
              (Correctors.reducedEnvironmentLaw_stationary Q),
            inner ℝ (Correctors.horizontalEuclideanGradient (Correctors.reducedEnvironmentLaw Q)
              (Correctors.reducedEnvironmentLaw_stationary Q) f)
              (Correctors.correctorFluxOfGradient Q i G') = 0) → G' = G) ∧
        (∀ j : Fin d, Correctors.euclideanCoordinateMean (Correctors.reducedEnvironmentLaw Q) j
          (correctorGradient Q i) = 0) ∧
        Integrable (Correctors.correctorFluxOfGradient Q i G) (reducedLaw Q) ∧
        ∀ j : Fin d, homogenizedCoefficient Q j i =
          (∫ ω, Correctors.correctorFluxOfGradient Q i G ω ∂reducedLaw Q) j

end EinsteinFull.Blueprint
