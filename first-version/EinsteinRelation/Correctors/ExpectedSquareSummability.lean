import EinsteinRelation.Correctors.CutoffErrorAlmostSure

/-! Source: `paper/main.tex:722,756`. The squared rounding errors have
summable expectations, so their literal local norms vanish almost surely. -/
open MeasureTheory Filter Topology
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Quadratically decaying expected squared errors are summable and give
almost sure convergence, including ENNReal-valued local norms. -/
theorem ae_tendsto_zero_of_expected_square_quadratic_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ≥0∞) (hm : ∀ n, AEMeasurable (X n) μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞)
    (hbound : ∀ n, (∫⁻ ω, (X n ω)^2 ∂μ) ≤
      M * ENNReal.ofReal (1 / ((n : ℝ) + 1)^2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_expected_square_summable μ X hm
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))))
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top hM.lt_top hs.tsum_ofReal_lt_top

end EinsteinRelation.Correctors
