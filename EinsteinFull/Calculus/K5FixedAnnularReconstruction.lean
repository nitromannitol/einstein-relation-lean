import Mathlib
import EinsteinFull.Calculus.K4AnnularCore

open MeasureTheory Filter Topology

namespace EinsteinFull.Calculus.K5

lemma toReal_eLpNorm_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {q : ENNReal}
    {f g : Ω → ℂ} (hq : 1 ≤ q) (hf : MemLp f q μ) (hg : MemLp g q μ) :
    (eLpNorm (f - g) q μ).toReal ≤ (eLpNorm f q μ).toReal + (eLpNorm g q μ).toReal := by
  have h : eLpNorm (f - g) q μ ≤ eLpNorm f q μ + eLpNorm g q μ := eLpNorm_sub_le (μ := μ) (f := f) (g := g) hq
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩) h

lemma sqrt_sum_mul_sq {ι : Type*} (Λ : Finset ι) (w : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (∑ z ∈ Λ, (a * w z) ^ 2) = a * Real.sqrt (∑ z ∈ Λ, w z ^ 2) := by
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

lemma tendsto_exp_neg_four_pow_mul {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => Real.exp (-4 ^ n * τ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (4 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h2 : Tendsto (fun n : ℕ => (4 : ℝ) ^ n * τ) atTop atTop :=
    h1.atTop_mul_const hτ
  have h3 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
  refine h3.congr (fun n => ?_)
  simp [neg_mul]

/-- Fixed-data annular reconstruction: the I1 contraction, a block bound `F * w z`, the I2
localization decay `L * exp (-4^n τ) * w z` and the I3 colored square sums give the
reconstructed block-sum bound, with the annular series constant written out. -/
theorem fixed_data_annular_reconstruction {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ} (hp : 1 ≤ p) (d : ℕ)
    (X : ι → Ω → ℂ) (CE : ℕ → ι → Ω → ℂ) (w : ι → ℝ) (F L τ c3 : ℝ)
    (hF : 0 ≤ F) (hL : 0 ≤ L) (hτ : 0 < τ) (hc3 : 0 ≤ c3) (hw : ∀ z, 0 ≤ w z)
    (hX : ∀ z, MemLp (X z) (ENNReal.ofReal p) μ)
    (hCE : ∀ n z, MemLp (CE n z) (ENNReal.ofReal p) μ)
    (h1 : ∀ z, (eLpNorm (CE 0 z) (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (X z) (ENNReal.ofReal p) μ).toReal)
    (hfb : ∀ z, (eLpNorm (X z) (ENNReal.ofReal p) μ).toReal ≤ F * w z)
    (h2 : ∀ n z, (eLpNorm (X z - CE n z) (ENNReal.ofReal p) μ).toReal ≤
      L * Real.exp (-4 ^ n * τ) * w z)
    (h3a : ∀ Λ : Finset ι, (eLpNorm (∑ z ∈ Λ, CE 0 z) (ENNReal.ofReal p) μ).toReal ≤
      c3 * Real.sqrt (∑ z ∈ Λ, ((eLpNorm (CE 0 z) (ENNReal.ofReal p) μ).toReal) ^ 2))
    (h3b : ∀ (n : ℕ) (Λ : Finset ι),
      (eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ).toReal ≤
        c3 * 2 ^ ((n : ℝ) * (d : ℝ) / 2) *
          Real.sqrt (∑ z ∈ Λ,
            ((eLpNorm (CE (n + 1) z - CE n z) (ENNReal.ofReal p) μ).toReal) ^ 2))
    (Λ : Finset ι) :
    MemLp (∑ z ∈ Λ, X z) (ENNReal.ofReal p) μ ∧
      (eLpNorm (∑ z ∈ Λ, X z) (ENNReal.ofReal p) μ).toReal ≤
        c3 * (F + 2 * L * ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
          Real.exp (-4 ^ n * τ)) * Real.sqrt (∑ z ∈ Λ, w z ^ 2) := by
  have hq : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  set S := Real.sqrt (∑ z ∈ Λ, w z ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hsum : Summable (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
      Real.exp (-4 ^ n * τ)) := K4.summable_two_rpow_mul_exp_neg_four_pow d hτ
  -- increment bound
  have hinc : ∀ n z, (eLpNorm (CE (n + 1) z - CE n z) (ENNReal.ofReal p) μ).toReal ≤
      2 * L * Real.exp (-4 ^ n * τ) * w z := by
    intro n z
    have hsub : CE (n + 1) z - CE n z = (X z - CE n z) - (X z - CE (n + 1) z) := by ring
    have hmem : ∀ m, MemLp (X z - CE m z) (ENNReal.ofReal p) μ := fun m => (hX z).sub (hCE m z)
    have h := toReal_eLpNorm_sub_le hq (hmem n) (hmem (n + 1))
    rw [hsub]
    have hexp : Real.exp (-4 ^ (n + 1) * τ) ≤ Real.exp (-4 ^ n * τ) := by
      apply Real.exp_le_exp.mpr
      have : (4 : ℝ) ^ n ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have e1 := h2 n z
    have e2 := h2 (n + 1) z
    have e3 : L * Real.exp (-4 ^ (n + 1) * τ) * w z ≤ L * Real.exp (-4 ^ n * τ) * w z := by
      gcongr
      exact hw z
    have e4 := toReal_eLpNorm_sub_le hq (hmem n) (hmem (n + 1))
    nlinarith
  have hbs : Summable (fun n : ℕ => c3 * 2 ^ ((n : ℝ) * (d : ℝ) / 2) *
      (2 * L * Real.exp (-4 ^ n * τ)) * S) := by
    have := (hsum.mul_left (c3 * (2 * L))).mul_right S
    refine this.congr (fun n => ?_)
    ring
  have hrem : ∀ z ∈ Λ, Tendsto (fun n => (eLpNorm (X z - CE n z) (ENNReal.ofReal p) μ).toReal)
      atTop (𝓝 0) := by
    intro z _
    have ht : Tendsto (fun n : ℕ => L * Real.exp (-4 ^ n * τ) * w z) atTop (𝓝 0) := by
      have := ((tendsto_exp_neg_four_pow_mul hτ).const_mul L).mul_const (w z)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun n => ENNReal.toReal_nonneg) (fun n => h2 n z)
  have ha : (eLpNorm (∑ z ∈ Λ, CE 0 z) (ENNReal.ofReal p) μ).toReal ≤ c3 * F * S := by
    refine (h3a Λ).trans ?_
    have : Real.sqrt (∑ z ∈ Λ, ((eLpNorm (CE 0 z) (ENNReal.ofReal p) μ).toReal) ^ 2) ≤
        F * S := by
      have h' : Real.sqrt (∑ z ∈ Λ, (F * w z) ^ 2) = F * S := sqrt_sum_mul_sq Λ w hF
      rw [← h']
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro z _
      have h0 : 0 ≤ (eLpNorm (CE 0 z) (ENNReal.ofReal p) μ).toReal := ENNReal.toReal_nonneg
      have := (h1 z).trans (hfb z)
      exact pow_le_pow_left₀ h0 this 2
    calc c3 * _ ≤ c3 * (F * S) := mul_le_mul_of_nonneg_left this hc3
      _ = c3 * F * S := by ring
  have hb : ∀ n, (eLpNorm (∑ z ∈ Λ, (CE (n + 1) z - CE n z)) (ENNReal.ofReal p) μ).toReal ≤
      c3 * 2 ^ ((n : ℝ) * (d : ℝ) / 2) * (2 * L * Real.exp (-4 ^ n * τ)) * S := by
    intro n
    refine (h3b n Λ).trans ?_
    have hc : 0 ≤ c3 * 2 ^ ((n : ℝ) * (d : ℝ) / 2) := by positivity
    have h' : Real.sqrt (∑ z ∈ Λ,
        ((eLpNorm (CE (n + 1) z - CE n z) (ENNReal.ofReal p) μ).toReal) ^ 2) ≤
        (2 * L * Real.exp (-4 ^ n * τ)) * S := by
      have e : Real.sqrt (∑ z ∈ Λ, (2 * L * Real.exp (-4 ^ n * τ) * w z) ^ 2) =
          (2 * L * Real.exp (-4 ^ n * τ)) * S :=
        sqrt_sum_mul_sq Λ w (by positivity)
      rw [← e]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro z _
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hinc n z) 2
    calc _ ≤ c3 * 2 ^ ((n : ℝ) * (d : ℝ) / 2) * ((2 * L * Real.exp (-4 ^ n * τ)) * S) :=
          mul_le_mul_of_nonneg_left h' hc
      _ = _ := by ring
  obtain ⟨hmem, hle⟩ := K4.annular_reconstruction_core hp X CE Λ hX hCE _ _ ha hb hbs hrem
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  have e : ∑' n : ℕ, c3 * 2 ^ ((n : ℝ) * (d : ℝ) / 2) * (2 * L * Real.exp (-4 ^ n * τ)) =
      c3 * (2 * L) * ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * τ) := by
    rw [← tsum_mul_left]
    congr 1
    ext n
    ring
  rw [tsum_mul_right, e]
  ring
end EinsteinFull.Calculus.K5
