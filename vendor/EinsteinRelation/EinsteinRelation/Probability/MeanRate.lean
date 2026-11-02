import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # The mean rate of a drift-plus-martingale process

Source: `paper/main.tex` 1144-1146. Let `Y τ = A τ + M τ`, where the drift part satisfies
`|A τ| ≤ B τ` and the martingale part satisfies `E[(M τ)²] ≤ C τ`. If `Y τ / τ → ℓ` in probability
as `τ → ∞`, then `E[A τ] / τ → ℓ`. Indeed `M τ / τ → 0` in probability by Chebyshev's inequality,
so `A τ / τ → ℓ` in probability, and `A τ / τ` is bounded.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Chebyshev's inequality for the martingale part, normalized by time. -/
theorem measureReal_le_of_sq_le {M : Ω → ℝ} (hint : Integrable (fun ω => M ω ^ 2) μ)
    {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | δ ≤ |M ω|} ≤ (∫ ω, M ω ^ 2 ∂μ) / δ ^ 2 := by
  have hset : {ω | δ ≤ |M ω|} ⊆ {ω | δ ^ 2 ≤ M ω ^ 2} := fun ω hω => by
    simp only [Set.mem_setOf_eq] at hω ⊢
    calc δ ^ 2 ≤ |M ω| ^ 2 := pow_le_pow_left₀ hδ.le hω 2
      _ = M ω ^ 2 := sq_abs _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg (M ω)) hint (δ ^ 2)
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hset) (by positivity)).trans hmarkov

/-- **Mean rate.** If `Y τ / τ → ℓ` in probability, `|A τ| ≤ B τ` almost surely, and the
martingale part `Y τ - A τ` has second moment at most `C τ`, then `E[A τ] / τ → ℓ`. -/
theorem tendsto_integral_div_of_sq_le (Y A : ℝ → Ω → ℝ) {ℓ B C : ℝ}
    (hAm : ∀ τ, Measurable (A τ))
    (hA : ∀ τ, 0 ≤ τ → ∀ᵐ ω ∂μ, |A τ ω| ≤ B * τ)
    (hMint : ∀ τ, 0 ≤ τ → Integrable (fun ω => (Y τ ω - A τ ω) ^ 2) μ)
    (hM2 : ∀ τ, 0 ≤ τ → ∫ ω, (Y τ ω - A τ ω) ^ 2 ∂μ ≤ C * τ)
    (hY : ∀ δ : ℝ, 0 < δ → Tendsto (fun τ => μ.real {ω | δ ≤ |Y τ ω / τ - ℓ|}) atTop (𝓝 0)) :
    Tendsto (fun τ => (∫ ω, A τ ω ∂μ) / τ) atTop (𝓝 ℓ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := |B| + |ℓ| with hKdef
  have hK : 0 ≤ K := by positivity
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set η : ℝ := ε / (4 * (K + 1)) with hηdef
  have hη : 0 < η := by positivity
  -- The velocity term is eventually small.
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hY (δ / 2) (by positivity)) η hη
  -- The Chebyshev term `4 C / (δ² τ)` is eventually small.
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℝ, ∀ τ ≥ N₂, 0 < τ → |C| / ((δ / 2) ^ 2 * τ) < η := by
    refine ⟨|C| / ((δ / 2) ^ 2 * η) + 1, fun τ hτ hτ0 => ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have h1 : |C| / ((δ / 2) ^ 2 * η) < τ := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith [h1]
  refine ⟨max (max N₁ N₂) 1, fun τ hτ => ?_⟩
  have hτ1 : 1 ≤ τ := le_of_max_le_right hτ
  have hτ0 : 0 < τ := by linarith
  have hτN₁ : N₁ ≤ τ := le_trans (le_max_left _ _) (le_of_max_le_left hτ)
  have hτN₂ : N₂ ≤ τ := le_trans (le_max_right _ _) (le_of_max_le_left hτ)
  -- The normalized drift `D = A τ / τ - ℓ` is bounded by `K`.
  set D : Ω → ℝ := fun ω => A τ ω / τ - ℓ with hDdef
  have hDm : Measurable D := ((hAm τ).div_const τ).sub_const ℓ
  have hDbd : ∀ᵐ ω ∂μ, |D ω| ≤ K := by
    filter_upwards [hA τ hτ0.le] with ω hω
    have : |A τ ω / τ| ≤ |B| := by
      rw [abs_div, abs_of_pos hτ0, div_le_iff₀ hτ0]
      exact hω.trans (mul_le_mul_of_nonneg_right (le_abs_self B) hτ0.le)
    calc |D ω| ≤ |A τ ω / τ| + |ℓ| := abs_sub _ _
      _ ≤ K := by rw [hKdef]; linarith
  have hDint : Integrable D μ :=
    (integrable_const K).mono' hDm.aestronglyMeasurable (hDbd.mono fun ω h => by
      rwa [Real.norm_eq_abs])
  -- The bad set `{δ ≤ |D|}` is covered by the two small sets.
  set S : Set Ω := {ω | δ ≤ |D ω|}
  have hSm : MeasurableSet S := measurableSet_le measurable_const (continuous_abs.measurable.comp hDm)
  have hcover : S ⊆ {ω | δ / 2 ≤ |Y τ ω / τ - ℓ|} ∪ {ω | δ / 2 * τ ≤ |Y τ ω - A τ ω|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    have hsplit : D ω = (Y τ ω / τ - ℓ) - (Y τ ω - A τ ω) / τ := by
      simp only [hDdef]; field_simp; ring
    have h2 : |(Y τ ω - A τ ω) / τ| < δ / 2 := by
      rw [abs_div, abs_of_pos hτ0, div_lt_iff₀ hτ0]; linarith [hcon.2]
    have : |D ω| < δ := by
      rw [hsplit]
      calc |(Y τ ω / τ - ℓ) - (Y τ ω - A τ ω) / τ| ≤ |Y τ ω / τ - ℓ| + |(Y τ ω - A τ ω) / τ| :=
            abs_sub _ _
        _ < δ / 2 + δ / 2 := add_lt_add hcon.1 h2
        _ = δ := by ring
    exact absurd hω (not_le.mpr this)
  have hcheb := measureReal_le_of_sq_le (μ := μ) (hMint τ hτ0.le) (show 0 < δ / 2 * τ by positivity)
  have hcheb' : μ.real {ω | δ / 2 * τ ≤ |Y τ ω - A τ ω|} < η := by
    refine hcheb.trans_lt ?_
    calc (∫ ω, (Y τ ω - A τ ω) ^ 2 ∂μ) / (δ / 2 * τ) ^ 2 ≤ (|C| * τ) / (δ / 2 * τ) ^ 2 := by
          gcongr
          exact (hM2 τ hτ0.le).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hτ0.le)
      _ = |C| / ((δ / 2) ^ 2 * τ) := by field_simp
      _ < η := hN₂ τ hτN₂ hτ0
  have hvel : μ.real {ω | δ / 2 ≤ |Y τ ω / τ - ℓ|} < η := by
    have := hN₁ τ hτN₁
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
  have hS : μ.real S < 2 * η := by
    calc μ.real S ≤ μ.real ({ω | δ / 2 ≤ |Y τ ω / τ - ℓ|} ∪ {ω | δ / 2 * τ ≤ |Y τ ω - A τ ω|}) :=
          measureReal_mono hcover
      _ ≤ μ.real {ω | δ / 2 ≤ |Y τ ω / τ - ℓ|} + μ.real {ω | δ / 2 * τ ≤ |Y τ ω - A τ ω|} :=
          measureReal_union_le _ _
      _ < η + η := add_lt_add hvel hcheb'
      _ = 2 * η := by ring
  -- `|D| ≤ δ + K 1_S`, so `E|D| ≤ δ + K μ(S) < ε`.
  have hpt : ∀ᵐ ω ∂μ, |D ω| ≤ δ + S.indicator (fun _ => K) ω := by
    filter_upwards [hDbd] with ω hω
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h]; linarith
    · rw [Set.indicator_of_notMem h]
      simp only [S, Set.mem_setOf_eq, not_le] at h
      linarith
  have hEabs : ∫ ω, |D ω| ∂μ ≤ δ + K * μ.real S := by
    have hind : Integrable (S.indicator fun _ : Ω => K) μ := (integrable_const K).indicator hSm
    calc ∫ ω, |D ω| ∂μ ≤ ∫ ω, (δ + S.indicator (fun _ => K) ω) ∂μ :=
          integral_mono_ae hDint.abs ((integrable_const δ).add hind) hpt
      _ = δ + K * μ.real S := by
          rw [integral_add (integrable_const δ) hind, integral_const, integral_indicator hSm,
            setIntegral_const]
          simp [mul_comm]
  have hmean : (∫ ω, A τ ω ∂μ) / τ - ℓ = ∫ ω, D ω ∂μ := by
    have hAint : Integrable (A τ) μ := by
      have : Integrable (fun ω => τ * (D ω + ℓ)) μ := (hDint.add (integrable_const ℓ)).const_mul τ
      refine this.congr (ae_of_all _ fun ω => ?_)
      simp only [hDdef]; field_simp; ring
    rw [show (fun ω => D ω) = fun ω => A τ ω / τ - ℓ from rfl, integral_sub (hAint.div_const τ)
      (integrable_const ℓ), integral_const, integral_div]
    simp
  rw [Real.dist_eq, hmean]
  calc |∫ ω, D ω ∂μ| ≤ ∫ ω, |D ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ δ + K * μ.real S := hEabs
    _ ≤ δ + K * (2 * η) := by gcongr
    _ < ε := by
        rw [hηdef, hδdef]
        have hK1 : K * (2 * (ε / (4 * (K + 1)))) ≤ ε / 2 := by
          rw [show K * (2 * (ε / (4 * (K + 1)))) = (ε / 2) * (K / (K + 1)) by field_simp; ring]
          exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
        linarith

end EinsteinRelation
