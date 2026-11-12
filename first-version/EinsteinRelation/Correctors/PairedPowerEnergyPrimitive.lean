import EinsteinRelation.Correctors.PairedSemigroupSpatialEnergy
import EinsteinRelation.Correctors.PowerCutoffEnergyFlux

/-! # The paired power-cutoff energy primitive

Source: `paper/main.tex:824–840`. The primitive concerns the literal
`χ^(2n)` energy and its precise weighted flux. Positive-time energy
continuity and the derivative of the cutoff power are both proved inputs.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual paired semigroup satisfies the power-cutoff endpoint
identity on every positive-time energy window.
Source: `paper/main.tex:814–840`. -/
theorem paired_semigroupSolutions_power_energy_integral_eq_sub
    {d : ℕ} {K a b : ℝ} (hK : 0 < K) (ha : 0 < a) (hab : a < b)
    {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)] (hA : Set.EqOn A₁ A₂ U)
    (hp₁ : IsParabolicSolution A₁ (Set.Ioo a b) U u₁ G₁)
    (hp₂ : IsParabolicSolution A₂ (Set.Ioo a b) U u₂ G₂)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in a..b,
      -2 * ∫ x in U, dot ((A₁ x).mulVec (G₁ (t,x) - G₂ (t,x))) (fun j =>
        χ x^(2*n) * (G₁ (t,x) - G₂ (t,x)) j +
          2 * (n : ℝ) * χ x^(2*n-1) * (u₁ (t,x) - u₂ (t,x)) * coordinateDerivative j χ x)) =
      (∫ x in U, χ x^(2*n) * (u₁ (b,x) - u₂ (b,x))^2) -
        (∫ x in U, χ x^(2*n) * (u₁ (a,x) - u₂ (a,x))^2) := by
  have hp := spatial_test_pow hχ n hn
  have h := paired_semigroupSolutions_spatial_energy_integral_eq_sub hK ha hab
    h₁ h₂ hU hUc hA hp₁ hp₂ hp.1 hp.2.1 hp.2.2
  simp only [spatial_energy_flux_pow A₁ (hχ.1.differentiable (by simp)) n hn] at h
  simpa only [← pow_mul, Nat.mul_comm n 2] using h

end EinsteinRelation.Correctors
