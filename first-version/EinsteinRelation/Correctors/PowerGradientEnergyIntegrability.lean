import EinsteinRelation.Correctors.ParabolicPowerEnergySlices

/-! # Integrability of the literal power-weighted dissipation

Source: `paper/main.tex:824–840`. The Euclidean gradient energy of the
actual solution is integrable on each supplied cylinder, and hence its
spatial integral is integrable in time.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A cutoff bounded between zero and one preserves the actual gradient
energy's integrability, including in the time variable.
Source: `paper/main.tex:824–840`. -/
theorem parabolicSolution_power_gradient_energy_integrable {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {χ : Vec d → ℝ} (hχ : Measurable χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (n : ℕ) :
    Integrable (fun z => χ z.2^(2*n) * euclideanSq (G z))
        (volume.restrict (I ×ˢ U)) ∧
      Integrable (fun t => ∫ x in U, χ x^(2*n) * euclideanSq (G (t,x)))
        (volume.restrict I) := by
  have hi : Integrable (fun z => euclideanSq (G z)) (volume.restrict (I ×ˢ U)) := by
    simpa only [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using
      hsol.2.2.1.integrable_sq
  have he : Integrable (fun z => χ z.2^(2*n) * euclideanSq (G z))
      (volume.restrict (I ×ˢ U)) := hi.bdd_mul
    ((hχ.comp measurable_snd).pow_const (2*n)).aestronglyMeasurable (by
      apply Filter.Eventually.of_forall
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hχb z.2).1 _)]
      exact pow_le_one₀ (hχb z.2).1 (hχb z.2).2)
  refine ⟨he, ?_⟩
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at he
  exact he.integral_prod_left

end EinsteinRelation.Correctors
