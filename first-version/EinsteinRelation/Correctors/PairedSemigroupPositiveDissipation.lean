import EinsteinRelation.Correctors.SemigroupParabolicOnPrecompact
import EinsteinRelation.Correctors.PairedParabolicEquation
import EinsteinRelation.Correctors.PowerGradientEnergyIntegrability

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Positive-time dissipation slices on one common event of times.
Source: `paper/main.tex:834–851`. -/
theorem paired_semigroup_power_gradient_integrable_positive_ae
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hA : Set.EqOn A₁ A₂ U)
    {χ : Vec d → ℝ} (hχm : Measurable χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (n : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
      Integrable (fun x => χ x^(2*n) * euclideanSq (G₁ (t,x) - G₂ (t,x)))
        (volume.restrict U) := by
  have hlocal (k m : ℕ) : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Set.Ioo (1 / ((k : ℝ) + 1)) ((m : ℝ) + 2) →
        Integrable (fun x => χ x^(2*n) * euclideanSq (G₁ (t,x) - G₂ (t,x)))
          (volume.restrict U) := by
    by_cases hab : 1 / ((k : ℝ) + 1) < (m : ℝ) + 2
    · apply (ae_restrict_iff' measurableSet_Ioo).mp
      have hp := paired_parabolicSolution hK measurableSet_Ioo hU.measurableSet hA
        (semigroupSolution_parabolic_on_precompact h₁ hU hUc (by positivity) hab)
        (semigroupSolution_parabolic_on_precompact h₂ hU hUc (by positivity) hab)
      have hi := (parabolicSolution_power_gradient_energy_integrable hp hχm hχb n).1
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
      exact hi.prod_right_ae
    · exact Filter.Eventually.of_forall fun t ht => False.elim (hab (ht.1.trans ht.2))
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards [ae_all_iff.mpr fun n => ae_all_iff.mpr (hlocal n)] with t ht
  intro ht0
  change 0 < t at ht0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht0
  obtain ⟨m, hm⟩ := exists_nat_gt t
  exact ht n m ⟨hn, hm.trans (by linarith)⟩

end EinsteinRelation.Correctors
