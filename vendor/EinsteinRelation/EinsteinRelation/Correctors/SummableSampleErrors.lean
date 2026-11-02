import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
/-- Summable annealed errors vanish samplewise; source `paper/main.tex:693-698`. -/
theorem ae_tendsto_zero_of_summable_integral_norm
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (H : ℕ → A → ℝ) (hH : ∀ n, Integrable (H n) μ)
    (hs : Summable (fun n => ∫ a, ‖H n a‖ ∂μ)) :
    ∀ᵐ a ∂μ, Tendsto (fun n => H n a) atTop (𝓝 0) := by
  have heq (n : ℕ) : (∫⁻ a, ‖H n a‖ₑ ∂μ) = ‖∫ a, ‖H n a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hH n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg fun a => abs_nonneg (H n a))]
    simp only [coe_nnnorm, Real.norm_eq_abs]
  have hsum : (∑' n, ∫⁻ a, ‖H n a‖ₑ ∂μ) ≠ ⊤ := by
    rw [funext heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs.abs)
  have hmeas (n : ℕ) : AEMeasurable (fun a => ‖H n a‖ₑ) μ := (hH n).1.enorm
  rw [← lintegral_tsum hmeas] at hsum
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hsum] with a ha
  have ha' : Summable (fun n => (‖H n a‖₊ : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact ha.ne
  exact ha'.of_norm.tendsto_atTop_zero
end EinsteinRelation.Correctors
