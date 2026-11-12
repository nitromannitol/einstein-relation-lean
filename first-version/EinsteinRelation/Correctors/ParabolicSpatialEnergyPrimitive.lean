import EinsteinRelation.Correctors.ParabolicSpatialEnergyTimeEquation
import EinsteinRelation.Correctors.WeakTimeFundamentalTheorem

/-! # The spatial energy primitive from the parabolic equation

Source: `paper/main.tex:824–840`. The actual weak time equation and the
energy class imply the integral identity once the literal energy is
continuous through the two endpoints. This isolates the trace regularity
needed when using canonical parabolic flows.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Endpoint identity for the actual spatial energy. Continuity is an
explicit regularity obligation; an energy primitive is not assumed.
Source: `paper/main.tex:824–840`. -/
theorem parabolicSolution_spatial_energy_integral_eq_sub {d : ℕ} {K a b : ℝ}
    (hK : 0 < K) (hab : a < b) {A : Coefficient d K} {U : Set (Vec d)}
    (hU : IsOpen U) {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U)
    (hE : ContinuousOn (fun t => ∫ x in U, ψ x ^ 2 * u (t,x) ^ 2) (Set.Icc a b)) :
    (∫ t in Set.Icc a b,
      -2 * ∫ x in U, dot ((A x).mulVec (G (t,x))) (fun j =>
        ψ x ^ 2 * G (t,x) j + 2 * ψ x * u (t,x) * coordinateDerivative j ψ x)) =
      (∫ x in U, ψ x ^ 2 * u (b,x) ^ 2) - (∫ x in U, ψ x ^ 2 * u (a,x) ^ 2) := by
  apply integral_eq_sub_of_weak_time_derivative hab _ _ hE
  · rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact (parabolicSolution_spatial_energy_time_integrable hK hsol hψ hψc).2
  · intro η hη hηc hηs
    exact parabolicSolution_spatial_energy_weak_time_equation hK hU hsol hψ hψc hψs
      hη hηc hηs

end EinsteinRelation.Correctors
