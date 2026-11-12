import EinsteinRelation.Correctors.SpatialEnergyFluxIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integrable time functions from the actual spatial energy

Source: `paper/main.tex:824–832`. Fubini turns the genuine parabolic energy
class into integrability of the literal weighted energy and its flux in time.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The compactly weighted scalar energy is integrable on the cylinder.
Source: `paper/main.tex:824–832`. -/
theorem parabolicSolution_spatial_energy_integrable {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z => ψ z.2 ^ 2 * u z ^ 2) (volume.restrict (I ×ˢ U)) := by
  obtain ⟨B, hB⟩ := hψc.exists_bound_of_continuous hψ.continuous
  exact hsol.1.integrable_sq.bdd_mul
    ((hψ.continuous.measurable.comp measurable_snd).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z : ℝ × Vec d =>
      show ‖ψ z.2 ^ 2‖ ≤ B ^ 2 by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB _) 2)

/-- The energy and its proposed weak time derivative are integrable time
functions, as a consequence of the actual parabolic energy class.
Source: `paper/main.tex:824–832`. -/
theorem parabolicSolution_spatial_energy_time_integrable {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun t => ∫ x in U, ψ x ^ 2 * u (t,x) ^ 2) (volume.restrict I) ∧
      Integrable (fun t => -2 * ∫ x in U, dot ((A x).mulVec (G (t,x))) (fun j =>
        ψ x ^ 2 * G (t,x) j + 2 * ψ x * u (t,x) * coordinateDerivative j ψ x))
        (volume.restrict I) := by
  have hprod : volume.restrict (I ×ˢ U) = (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hE := parabolicSolution_spatial_energy_integrable hsol hψ hψc
  have hP := parabolicSolution_spatial_energy_flux_integrable hK A hsol hψ hψc
  rw [hprod] at hE hP
  exact ⟨hE.integral_prod_left, hP.integral_prod_left.const_mul (-2)⟩

end EinsteinRelation.Correctors
