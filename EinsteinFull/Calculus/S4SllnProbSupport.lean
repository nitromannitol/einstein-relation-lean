import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.PSeries

/-!
# Chebyshev and Borel–Cantelli along the squares

If `∫ X_n² ≤ B n²` for all `n`, then `X_n / n² → 0` almost surely.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinFull

theorem prob_ge_le_of_lintegral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) {c : ℝ} (hc : 0 < c) :
    P {ω | c ≤ |X ω|} ≤ (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P) / ENNReal.ofReal (c ^ 2) := by
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (X ω ^ 2)) P :=
    (ENNReal.measurable_ofReal.comp (hX.pow_const 2)).aemeasurable
  have h := meas_ge_le_lintegral_div hm (ε := ENNReal.ofReal (c ^ 2))
    (ENNReal.ofReal_pos.2 (pow_pos hc 2)).ne' ENNReal.ofReal_ne_top
  refine le_trans (measure_mono fun ω hω => ?_) h
  have hω' : c ≤ |X ω| := hω
  show ENNReal.ofReal (c ^ 2) ≤ ENNReal.ofReal (X ω ^ 2)
  refine ENNReal.ofReal_le_ofReal ?_
  have := pow_le_pow_left₀ hc.le hω' 2
  rwa [sq_abs] at this

theorem ae_tendsto_div_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n)) {B : ℝ}
    (hB : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (X n ω ^ 2) ∂P ≤ ENNReal.ofReal (B * (n : ℝ) ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => X n ω / (n : ℝ) ^ 2) atTop (𝓝 0) := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, |X n ω| < ε * (n : ℝ) ^ 2 := by
    intro ε hε
    set s : ℕ → Set Ω := fun n => {ω | ε * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ |X (n + 1) ω|} with hs
    have hle : ∀ n, P (s n) ≤
        ENNReal.ofReal (max B 0 / ε ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) := by
      intro n
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have h1 := prob_ge_le_of_lintegral_sq (P := P) (hX (n + 1))
        (c := ε * ((n + 1 : ℕ) : ℝ) ^ 2) (by positivity)
      refine h1.trans ?_
      refine (ENNReal.div_le_div_right (hB (n + 1)) _).trans ?_
      rw [← ENNReal.ofReal_div_of_pos (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hn' := hn.ne'
      have hε' := hε.ne'
      calc B * ((n + 1 : ℕ) : ℝ) ^ 2 / (ε * ((n + 1 : ℕ) : ℝ) ^ 2) ^ 2
          = B / ε ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by field_simp
        _ ≤ max B 0 / ε ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
            gcongr
            exact le_max_left _ _
    have hsumm : Summable (fun n : ℕ => max B 0 / ε ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) := by
      have h0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.2 one_lt_two
      exact ((summable_nat_add_iff 1).2 h0).mul_left _
    have hsum : ∑' n, P (s n) ≠ ∞ := by
      have h2 : ∑' n, P (s n) ≤ ∑' n : ℕ,
          ENNReal.ofReal (max B 0 / ε ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
        ENNReal.tsum_le_tsum hle
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm] at h2
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hω
    rw [Filter.eventually_atTop]
    refine ⟨N + 1, fun m hm => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have h := hN n (by omega)
    simpa only [hs, Set.mem_setOf_eq, not_le] using h
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |X n ω| < (1 / ((k : ℝ) + 1)) * (n : ℝ) ^ 2 :=
    ae_all_iff.2 fun k => key _ (by positivity)
  filter_upwards [hall] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hω k)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have h := hN n (le_trans (le_max_left _ _) hn)
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  calc |X n ω| < 1 / ((k : ℝ) + 1) * (n : ℝ) ^ 2 := h
    _ ≤ ε * (n : ℝ) ^ 2 := by gcongr

end EinsteinFull
