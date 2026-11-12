import EinsteinRelation.Correctors.ParabolicPowerEnergySlices
import EinsteinRelation.Correctors.SpatialEnergyFluxInterpolation

/-! # Spatial interpolation for the actual weak energy dynamics

Source: `paper/main.tex:824–832`. The actual energy-class solution
supplies every slice integrability premise; coercivity and spatial Hölder
then control the signed time flux plus the literal Euclidean dissipation.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The scalar derivative proxy from the genuine weak time equation
satisfies the manuscript's interpolated energy inequality at almost
every time. Source: `paper/main.tex:824–832`. -/
theorem parabolicSolution_power_energy_inequality_ae {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {L : ℝ} (hD : ∀ x, euclideanSq (gradient χ x) ≤ L^2)
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ t ∂volume.restrict I,
      (-2 * ∫ x in U, dot ((A x).mulVec (G (t,x))) (fun j =>
        χ x^(2*n) * G (t,x) j +
          2 * (n : ℝ) * χ x^(2*n-1) * u (t,x) * coordinateDerivative j χ x)) +
        (∫ x in U, χ x^(2*n) * euclideanSq (G (t,x))) ≤
          (4 * (n : ℝ)^2 * K^2 * L^2) *
            ((∫ x in U, χ x^(2*n) * u (t,x)^2) ^ (1 - (n : ℝ)⁻¹) *
              (∫ x in U, u (t,x)^2) ^ ((n : ℝ)⁻¹)) := by
  filter_upwards [parabolicSolution_power_energy_slices hK hsol hχ n (by omega)] with t ht
  exact integral_energy_flux_interpolation hK A (volume.restrict U)
    hχ.1.continuous.measurable hχb ht.1 ht.2.1 hD n hn ht.2.2

end EinsteinRelation.Correctors
