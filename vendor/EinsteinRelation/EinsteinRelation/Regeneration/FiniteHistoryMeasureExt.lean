import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Probability.FiniteHistoryExhaustion
import EinsteinRelation.Probability.IncreasingSigmaMeasureExt
import EinsteinRelation.Probability.FiniteHistoryStopping

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:377–402`: bounded exact-history tests determine the whole coupled law. -/
theorem measure_eq_of_finite_history_integrals {d : ℕ}
    (μ ν : Measure (CoupledSample d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ F : CoupledSample d → ℝ,
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F →
      BoundedRealTest F → (∫ z, F z ∂μ) = ∫ z, F z ∂ν) : μ = ν := by
  apply Probability.measure_eq_of_increasing_sigma μ ν (finiteHistorySigma Δ)
    (fun _ _ h => finiteHistorySigma_mono Δ h) (iSup_finiteHistorySigma_eq Δ hΔ)
  intro n s hs
  have hs' := Probability.finiteHistorySigma_le (d := d) Δ n s hs
  have ht := h (max n 1) (le_max_right _ _)
    (s.indicator (1 : CoupledSample d → ℝ))
    (measurable_const.indicator
      (finiteHistorySigma_mono Δ (le_max_left n 1) s hs))
    ⟨1, fun z => by by_cases hz : z ∈ s <;> simp [hz]⟩
  rw [integral_indicator_one hs', integral_indicator_one hs'] at ht
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top ν s)).mp ht

end EinsteinRelation.Regeneration
