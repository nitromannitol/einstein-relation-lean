import EinsteinFull.Frozen.ReducedLaw
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The blueprint's unique mean-zero stationary potential corrector gradient.
It is constructed by the proved coercive variational problem, including in d=2. -/
noncomputable def correctorGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) :=
  (Correctors.canonicalCorrectorGradient Q i).val

end EinsteinFull
