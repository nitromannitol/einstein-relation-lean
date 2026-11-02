import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment_u23_canonical_u2D_law
import EinsteinRelation.Correctors.HorizontalCharacterizationSupport
import EinsteinRelation.Correctors.HorizontalH1SpatialGradient
import EinsteinRelation.Correctors.HorizontalH1FullIbP

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `stationary-environment`, `paper/main.tex:236–240`.
The actual reduced-law translation representation is a strongly continuous
unitary group. Its full horizontal H1 domain has the distributional
characterization, the actual samplewise spatial weak gradient, and full-domain
integration by parts. No smoothness or diffusion identification is assumed. -/
def node_stationary_u2D_environmentStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    let P := Correctors.reducedEnvironmentLaw Q
    let hP := Correctors.reducedEnvironmentLaw_stationary Q
    (∀ f : Lp ℝ 2 P, translationLp P hP 0 f = f) ∧
    (∀ (x y : Vec d) (f : Lp ℝ 2 P),
      translationLp P hP (x + y) f = translationLp P hP x (translationLp P hP y f)) ∧
    (∀ (x : Vec d) (f : Lp ℝ 2 P), ‖translationLp P hP x f‖ = ‖f‖) ∧
    (∀ x : Vec d, Function.Surjective (translationLp P hP x)) ∧
    Continuous (fun p : Vec d × Lp ℝ 2 P => translationLp P hP p.1 p.2) ∧
    (∀ f : Lp ℝ 2 P, f ∈ horizontalH1 P hP ↔
      ∀ i : Fin d, ∃ g : Lp ℝ 2 P, Correctors.HasWeakHorizontalLpDerivative P i f g) ∧
    (∀ (f : horizontalH1 P hP) (i : Fin d),
      HasHorizontalLpDerivative P hP i f (horizontalH1Gradient P hP f i)) ∧
    (∀ f : horizontalH1 P hP,
      (∀ᵐ ω ∂P, HasWeakGradient Set.univ
        (fun x => (f : Lp ℝ 2 P) (translate x ω))
        (fun x => (Correctors.horizontalEuclideanGradient P hP f (translate x ω)).ofLp)) ∧
      ∀ (g : horizontalH1 P hP) (i : Fin d),
        Integrable (fun ω => (horizontalH1Gradient P hP f i) ω * (g : Lp ℝ 2 P) ω) P ∧
        Integrable (fun ω => (f : Lp ℝ 2 P) ω * (horizontalH1Gradient P hP g i) ω) P ∧
        (∫ ω, (horizontalH1Gradient P hP f i) ω * (g : Lp ℝ 2 P) ω ∂P) =
          -(∫ ω, (f : Lp ℝ 2 P) ω * (horizontalH1Gradient P hP g i) ω ∂P))

end EinsteinFull.Blueprint
