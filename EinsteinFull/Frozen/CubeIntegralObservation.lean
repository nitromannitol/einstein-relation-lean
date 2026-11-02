import EinsteinFull.Frozen.ComplexTranslation
import EinsteinFull.Frozen.ReducedLawStationary
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- The actual unnormalized stationary integral over a cube of side rho.
The cube is centered at the origin; translating gives every source cube. -/
noncomputable def cubeIntegralObservation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ρ : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) :=
  ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2)),
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U

end EinsteinFull
