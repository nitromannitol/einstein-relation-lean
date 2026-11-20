import EinsteinFull.Homogenization.SourceOptimizerBookMoment
import Homogenization.Sobolev.Foundations.DifferenceQuotient

/-!
# Normalized square averages

For a square-integrable function, the square of the normalized cube `L²` norm
is the normalized spatial average of its square. This identifies the norm in
the optimizer flatness estimate of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, (2.47).
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- The normalized cube `L²` norm squared equals the integrable spatial
average of the square. -/
theorem integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Integrable (fun x => (f x) ^ 2) (normalizedCubeMeasure Q) ∧
      (cubeLpNorm Q 2 f) ^ 2 = cubeAverage Q (fun x => (f x) ^ 2) := by
  refine ⟨hf.integrable_sq, ?_⟩
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact toReal_eLpNorm_two_sq_eq_integral_sq hf

end EinsteinFull.Homogenization
