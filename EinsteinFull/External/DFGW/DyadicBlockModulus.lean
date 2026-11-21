import EinsteinFull.External.DFGW.DynkinDyadicMaximal
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Moduli of continuity from dyadic block increments

A continuous function on `[0, 1]` whose increments from the left endpoint of each of the `2 ^ a`
blocks of length `2 ^ (-a)` to the dyadic points of that block are at most `ρ` has oscillation at
most `3 ρ` at scale `2 ^ (-a)`.
-/

open Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

/-- The real value of a dyadic grid point. -/
theorem coe_dyadicGridTime (t : ℝ≥0) (r k : ℕ) :
    ((dyadicGridTime t r k : ℝ≥0) : ℝ) = k * ((t : ℝ) / 2 ^ r) := by
  simp only [dyadicGridTime, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast]
  push_cast
  ring

/-- Control of the dyadic increments of a block extends to the whole block by continuity. -/
theorem abs_sub_le_of_dyadic_block {z : ℝ≥0 → ℝ} (hz : Continuous z) {x δ : ℝ≥0} {ρ : ℝ}
    (hblock : ∀ r k : ℕ, k ≤ 2 ^ r → |z (x + dyadicGridTime δ r k) - z x| ≤ ρ)
    {u : ℝ≥0} (hxu : x ≤ u) (hux : u ≤ x + δ) : |z u - z x| ≤ ρ := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ δ) with hδ | hδ
  · rw [← hδ, add_zero] at hux
    have : u = x := le_antisymm hux hxu
    rw [this, sub_self, abs_zero]
    have h := hblock 0 0 (Nat.zero_le _)
    simpa [dyadicGridTime] using h
  have hδr : (0 : ℝ) < δ := hδ
  let q : ℝ := ((u : ℝ) - x) / δ
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.2 (by exact_mod_cast hxu)) hδr.le
  have hq1 : q ≤ 1 := by
    rw [div_le_one hδr]
    have : (u : ℝ) ≤ x + δ := by exact_mod_cast hux
    linarith
  let k : ℕ → ℕ := fun r => ⌊q * 2 ^ r⌋₊
  have hk (r : ℕ) : k r ≤ 2 ^ r := by
    apply Nat.floor_le_of_le
    push_cast
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) r]
  let v : ℕ → ℝ≥0 := fun r => x + dyadicGridTime δ r (k r)
  have hv : Tendsto v atTop (𝓝 u) := by
    rw [← NNReal.tendsto_coe]
    have hfloor := (tendsto_nat_floor_mul_div_atTop hq0).comp
      (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num))
    have hlim : Tendsto (fun r : ℕ => (x : ℝ) + δ * ((⌊q * 2 ^ r⌋₊ : ℝ) / 2 ^ r)) atTop
        (𝓝 ((x : ℝ) + δ * q)) :=
      tendsto_const_nhds.add (hfloor.const_mul _)
    have hu : (x : ℝ) + δ * q = u := by
      dsimp only [q]
      field_simp
      ring
    rw [hu] at hlim
    apply hlim.congr'
    filter_upwards with r
    simp only [v, NNReal.coe_add, coe_dyadicGridTime, k]
    ring
  have hlimz : Tendsto (fun r => |z (v r) - z x|) atTop (𝓝 (|z u - z x|)) :=
    (((hz.tendsto u).comp hv).sub tendsto_const_nhds).abs
  exact le_of_tendsto' hlimz fun r => hblock r (k r) (hk r)

/-- **Block criterion.** If every increment from the left endpoint of one of the `2 ^ a` blocks of
`[0, 1]` to a dyadic point of that block is at most `ρ`, then any two times of `[0, 1]` at
distance at most `2 ^ (-a)` carry values within `3 ρ`. -/
theorem abs_sub_le_of_dyadic_blocks {z : ℝ≥0 → ℝ} (hz : Continuous z) (a : ℕ) {ρ : ℝ}
    (hblocks : ∀ j < 2 ^ a, ∀ r k : ℕ, k ≤ 2 ^ r →
      |z (j • ((2 : ℝ≥0) ^ a)⁻¹ + dyadicGridTime ((2 : ℝ≥0) ^ a)⁻¹ r k) -
        z (j • ((2 : ℝ≥0) ^ a)⁻¹)| ≤ ρ)
    {s t : ℝ≥0} (hs : s ≤ 1) (ht : t ≤ 1) (hst : |(s : ℝ) - t| ≤ (2 ^ a : ℝ)⁻¹) :
    |z s - z t| ≤ 3 * ρ := by
  let δ : ℝ≥0 := ((2 : ℝ≥0) ^ a)⁻¹
  have hδr : ((δ : ℝ≥0) : ℝ) = (2 ^ a : ℝ)⁻¹ := by simp [δ]
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  have hρ : 0 ≤ ρ := by
    have h := hblocks 0 (by positivity) 0 0 (Nat.zero_le _)
    exact (abs_nonneg _).trans h
  have hjδ (j : ℕ) : ((j • δ : ℝ≥0) : ℝ) = j / 2 ^ a := by
    rw [nsmul_eq_mul, NNReal.coe_mul, hδr]
    push_cast
    ring
  have hblock (j : ℕ) (hj : j < 2 ^ a) (u : ℝ≥0) (h1 : (j : ℝ) / 2 ^ a ≤ u)
      (h2 : (u : ℝ) ≤ (j + 1) / 2 ^ a) : |z u - z (j • δ)| ≤ ρ := by
    apply abs_sub_le_of_dyadic_block hz (hblocks j hj)
    · rw [← NNReal.coe_le_coe, hjδ]
      exact h1
    · rw [← NNReal.coe_le_coe, NNReal.coe_add, hjδ, hδr]
      calc
        (u : ℝ) ≤ (j + 1) / 2 ^ a := h2
        _ = j / 2 ^ a + (2 ^ a)⁻¹ := by field_simp
  -- reduce to `s ≤ t`
  wlog hle : s ≤ t generalizing s t
  · have h := this ht hs (by rwa [abs_sub_comm]) (le_of_not_ge hle)
    rwa [abs_sub_comm]
  rcases eq_or_lt_of_le hs with hs1 | hs1
  · have ht1 : t = 1 := le_antisymm ht (hs1 ▸ hle)
    rw [hs1, ht1, sub_self, abs_zero]
    positivity
  have hs1r : (s : ℝ) < 1 := by exact_mod_cast hs1
  let j : ℕ := ⌊(s : ℝ) * 2 ^ a⌋₊
  have hj1 : (j : ℝ) ≤ s * 2 ^ a := Nat.floor_le (by positivity)
  have hj2 : (s : ℝ) * 2 ^ a < j + 1 := Nat.lt_floor_add_one _
  have hjlt : j < 2 ^ a := by
    have : (j : ℝ) < 2 ^ a := by nlinarith
    exact_mod_cast this
  have hsl : (j : ℝ) / 2 ^ a ≤ s := by rw [div_le_iff₀ h2a]; exact hj1
  have hsr : (s : ℝ) ≤ (j + 1) / 2 ^ a := by rw [le_div_iff₀ h2a]; exact hj2.le
  have hts : (t : ℝ) - s ≤ (2 ^ a)⁻¹ := by
    have h := le_abs_self ((t : ℝ) - s)
    rw [abs_sub_comm] at hst
    linarith
  have hS := hblock j hjlt s hsl hsr
  have hstr : (s : ℝ) ≤ t := by exact_mod_cast hle
  by_cases hcase : (t : ℝ) ≤ (j + 1) / 2 ^ a
  · have hT := hblock j hjlt t (hsl.trans hstr) hcase
    calc
      |z s - z t| ≤ |z s - z (j • δ)| + |z t - z (j • δ)| := by
        rw [abs_sub_comm (z t)]
        exact abs_sub_le _ _ _
      _ ≤ 3 * ρ := by linarith
  · rw [not_le] at hcase
    have hj1lt : j + 1 < 2 ^ a := by
      have ht1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
      have : ((j : ℝ) + 1) < 2 ^ a := by
        rw [div_lt_iff₀ h2a] at hcase
        nlinarith
      exact_mod_cast this
    have hmid : |z ((j + 1) • δ) - z (j • δ)| ≤ ρ := by
      apply hblock j hjlt
      · rw [hjδ]
        push_cast
        gcongr
        linarith
      · rw [hjδ]
        push_cast
        exact le_rfl
    have htl : ((j + 1 : ℕ) : ℝ) / 2 ^ a ≤ t := by push_cast; exact hcase.le
    have htr : (t : ℝ) ≤ ((j + 1 : ℕ) + 1) / 2 ^ a := by
      push_cast
      have : (t : ℝ) ≤ s + (2 ^ a)⁻¹ := by linarith
      calc
        (t : ℝ) ≤ s + (2 ^ a)⁻¹ := this
        _ ≤ (j + 1) / 2 ^ a + (2 ^ a)⁻¹ := by linarith
        _ = (j + 1 + 1) / 2 ^ a := by field_simp
    have hT := hblock (j + 1) hj1lt t htl htr
    calc
      |z s - z t| ≤ |z s - z (j • δ)| + |z ((j + 1) • δ) - z (j • δ)| +
          |z t - z ((j + 1) • δ)| := by
        have h1 := abs_sub_le (z s) (z (j • δ)) (z t)
        have h2 := abs_sub_le (z (j • δ)) (z ((j + 1) • δ)) (z t)
        rw [abs_sub_comm (z (j • δ)) (z ((j + 1) • δ))] at h2
        rw [abs_sub_comm (z ((j + 1) • δ)) (z t)] at h2
        linarith
      _ ≤ 3 * ρ := by linarith

end EinsteinFull.External.DFGW
