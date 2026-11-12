import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries

/-! Source: `paper/main.tex:722,756`. Square-summable expected cutoff
errors converge to zero almost surely. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

/-- Finiteness of the sum of expected squared errors gives almost sure
convergence of the actual ENNReal error norms. -/
theorem ae_tendsto_zero_of_expected_square_summable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ENNReal)
    (hm : ∀ n, AEMeasurable (X n) μ)
    (hsum : (∑' n, ∫⁻ ω, (X n ω)^2 ∂μ) < ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  have hi : (∫⁻ ω, ∑' n, (X n ω)^2 ∂μ) < ⊤ := by
    rw [lintegral_tsum (fun n => (hm n).pow_const 2)]
    exact hsum
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum (fun n => (hm n).pow_const 2))
    hi.ne] with ω hω
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp ht (ε^2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp (hN n hn)

end EinsteinRelation.Correctors
