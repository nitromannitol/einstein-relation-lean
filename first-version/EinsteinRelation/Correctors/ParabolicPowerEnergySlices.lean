import EinsteinRelation.Correctors.PowerCutoffEnergyFlux

/-! # Actual spatial slices for the power-cutoff energy equation

Source: `paper/main.tex:824–832`. Fubini supplies the square-integrable
scalar and Euclidean gradient slices and the integrable literal flux
required to apply spatial coercivity. No prescribed-time gradient values
are assumed or chosen.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual parabolic energy class supplies all three spatial
integrability premises simultaneously at almost every time.
Source: `paper/main.tex:824–832`. -/
theorem parabolicSolution_power_energy_slices {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ t ∂volume.restrict I,
      MemLp (fun x => u (t,x)) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (G (t,x))) 2 (volume.restrict U) ∧
      Integrable (fun x => dot ((A x).mulVec (G (t,x))) (fun j =>
        χ x^(2*n) * G (t,x) j +
          2 * (n : ℝ) * χ x^(2*n-1) * u (t,x) * coordinateDerivative j χ x))
        (volume.restrict U) := by
  have hprod : volume.restrict (I ×ˢ U) =
      (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hu := hsol.1
  have hG := hsol.2.2.1
  have hp := spatial_test_pow hχ n hn
  have hP := parabolicSolution_spatial_energy_flux_integrable hK A hsol hp.1 hp.2.1
  simp only [spatial_energy_flux_pow A (hχ.1.differentiable (by simp)) n hn] at hP
  rw [hprod] at hu hG hP
  filter_upwards [hu.1.prodMk_left, hG.1.prodMk_left,
    hu.integrable_sq.prod_right_ae, hG.integrable_sq.prod_right_ae,
    hP.prod_right_ae] with t hum hGm hui hGi hPi
  exact ⟨(memLp_two_iff_integrable_sq hum).mpr hui,
    (memLp_two_iff_integrable_sq hGm).mpr hGi, hPi⟩

end EinsteinRelation.Correctors
