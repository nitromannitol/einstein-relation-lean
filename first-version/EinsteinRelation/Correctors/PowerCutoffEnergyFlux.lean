import EinsteinRelation.Correctors.ParabolicSpatialEnergyTimeEquation
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! # Literal flux for a spatial cutoff power

Source: `paper/main.tex:824–832`. The energy flux for the multiplier
`χ^n` is the flux paired with `χ^(2n) u`. The chain rule below keeps
both the scalar and gradient fields unchanged.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The smooth power has the precise flux used in the weighted energy
argument. Source: `paper/main.tex:824–832`. -/
theorem spatial_energy_flux_pow {d : ℕ} {K : ℝ} (A : Coefficient d K)
    {χ : Vec d → ℝ} (hχ : Differentiable ℝ χ) (n : ℕ) (hn : 1 ≤ n)
    (x : Vec d) (v : ℝ) (G : Vec d) :
    dot ((A x).mulVec G) (fun j => (χ x ^ n)^2 * G j +
      2 * χ x ^ n * v * coordinateDerivative j (fun y => χ y ^ n) x) =
    dot ((A x).mulVec G) (fun j => χ x ^ (2*n) * G j +
      2 * (n : ℝ) * χ x ^ (2*n-1) * v * coordinateDerivative j χ x) := by
  have hd (j : Fin d) : coordinateDerivative j (fun y => χ y ^ n) x =
      (n : ℝ) * χ x ^ (n-1) * coordinateDerivative j χ x := by
    dsimp only [coordinateDerivative]
    rw [((hχ x).hasFDerivAt.pow n).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
  have hp : (χ x ^ n)^2 = χ x^(2*n) := by rw [← pow_mul, Nat.mul_comm]
  have hc : χ x^n * χ x^(n-1) = χ x^(2*n-1) := by
    rw [← pow_add, show n + (n-1) = 2*n-1 by omega]
  unfold dot
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [hp, hd j]
  have hcross : 2 * χ x^n * v * ((n : ℝ) * χ x^(n-1) * coordinateDerivative j χ x) =
      2 * (n : ℝ) * χ x^(2*n-1) * v * coordinateDerivative j χ x := by
    calc
      _ = 2 * (n : ℝ) * (χ x^n * χ x^(n-1)) * v * coordinateDerivative j χ x := by ring
      _ = _ := by rw [hc]
  rw [hcross]

/-- Positive powers preserve the spatial test domain and compact support.
Source: `paper/main.tex:824–832`. -/
theorem spatial_test_pow {d : ℕ} {U : Set (Vec d)} {χ : Vec d → ℝ}
    (hχ : IsSpatialTest U χ) (n : ℕ) (hn : 1 ≤ n) :
    IsSpatialTest U (fun x => χ x^n) := by
  have heq : (fun x => χ x^n) = (fun x => χ x * χ x^(n-1)) := by
    funext x
    rw [← pow_succ', Nat.sub_add_cancel hn]
  refine ⟨hχ.1.pow n, ?_, ?_⟩
  · rw [heq]
    exact hχ.2.1.mul_right
  · rw [heq]
    exact tsupport_mul_subset_left.trans hχ.2.2

/-- The energy class gives integrability of the exact scalar energy and
power-cutoff flux in time. Source: `paper/main.tex:824–832`. -/
theorem parabolicSolution_power_energy_time_integrable {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun t => ∫ x in U, χ x^(2*n) * u (t,x)^2) (volume.restrict I) ∧
      Integrable (fun t => -2 * ∫ x in U, dot ((A x).mulVec (G (t,x))) (fun j =>
        χ x^(2*n) * G (t,x) j +
          2 * (n : ℝ) * χ x^(2*n-1) * u (t,x) * coordinateDerivative j χ x))
        (volume.restrict I) := by
  have hp := spatial_test_pow hχ n hn
  have heq (x : Vec d) : (χ x^n)^2 = χ x^(2*n) := by rw [← pow_mul, Nat.mul_comm]
  have ht := parabolicSolution_spatial_energy_time_integrable hK hsol hp.1 hp.2.1
  refine ⟨by simpa only [heq] using ht.1, ?_⟩
  simpa only [spatial_energy_flux_pow A (hχ.1.differentiable (by simp)) n hn] using ht.2

end EinsteinRelation.Correctors
