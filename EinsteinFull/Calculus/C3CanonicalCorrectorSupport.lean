import EinsteinRelation.Correctors.AKMGlobalCorrectorConstruction
import EinsteinFull.Calculus.C2BallPoincareFromPDE

/-! The canonical corrector producer specialized to the proved Euclidean ball Poincaré estimate. -/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Correctors
open EinsteinRelation.External.AKM EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.ReductionImageV3

/-- The actual global AKM corrector with the ball Poincaré input discharged by PDEFoundation. -/
theorem exists_akmCorrector_global_gradient_identification_from_pde
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ φ : Corrector (actualCoefficientLaw Q) (halfDirection i),
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i +
          φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp := by
  exact exists_akmCorrector_global_gradient_identification ballPoincareEstimate_from_pde Q i

end EinsteinFull
