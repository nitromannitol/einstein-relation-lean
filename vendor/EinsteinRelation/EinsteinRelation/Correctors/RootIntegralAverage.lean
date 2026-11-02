import EinsteinRelation.Correctors.SpatialBallTranslation

/-! Source: `paper/main.tex:718-723`. Convert the normalized local L²
oscillation from AKM to the unnormalized root integral used in local
elliptic estimates, retaining the actual ball volume. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- The root integral is the root average multiplied by the square root
of the mass. The positivity condition excludes zero and infinite mass. -/
theorem sqrt_integral_eq_sqrt_mass_mul_sqrt_average
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hμ : 0 < μ.real Set.univ) :
    Real.sqrt (∫ x, f x ∂μ) =
      Real.sqrt (μ.real Set.univ) * Real.sqrt (⨍ x, f x ∂μ) := by
  rw [average_eq, smul_eq_mul, ← Real.sqrt_mul hμ.le,
    ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]

/-- Coordinate Lebesgue volume of a Euclidean ball is independent of its center. -/
theorem volume_euclideanBall_center {d : ℕ} (z : Vec d) (R : ℝ) :
    volume (ball z R) = volume (ball (0 : Vec d) R) := by
  have h := (measurePreserving_add_center_ball z R).measure_preimage
    MeasurableSet.univ.nullMeasurableSet
  simpa using h.symm

end EinsteinRelation.Correctors
