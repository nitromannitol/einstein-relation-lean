import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Source: `paper/main.tex:722,756`. Relative lengths of the windows
joining a positive cutoff to the original integer/reciprocal meshes. -/
namespace EinsteinRelation.Correctors

/-- Rounding a positive time upward to the integer mesh loses relative
length at most `1/s`; rounding downward to the reciprocal mesh loses
relative length at most `s`. Both rounded times are strictly positive. -/
theorem cutoff_nearest_mesh_ratios {s : ℝ} (hs : 0 < s) :
    (let t : ℝ := ((⌊s⌋₊ + 1 : ℕ) : ℝ)
     0 < t ∧ s < t ∧ (t - s) / s ≤ 1 / s) ∧
    (let t : ℝ := (((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹
     0 < t ∧ t < s ∧ (s - t) / t ≤ s) := by
  have hs_nonneg : 0 ≤ s := hs.le
  have hsinv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs_nonneg
  have hs_pos' : 0 < s⁻¹ := inv_pos.mpr hs
  constructor
  · -- Part 1: rounding s upward to integer mesh ⌊s⌋₊ + 1
    set t : ℝ := ((⌊s⌋₊ + 1 : ℕ) : ℝ) with ht_def
    have ht_pos : 0 < t := by
      rw [ht_def]
      have h_one_le : (1 : ℕ) ≤ ⌊s⌋₊ + 1 := by omega
      exact mod_cast Nat.one_pos.trans_le h_one_le
    have hs_lt_t : s < t := by
      rw [ht_def]
      have h_lt : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
      simpa [Nat.cast_add, Nat.cast_one] using h_lt
    have h_ratio : (t - s) / s ≤ 1 / s := by
      have h_sub_le_one : t - s ≤ 1 := by
        rw [ht_def]
        have h_floor_le : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs_nonneg
        have h : ((⌊s⌋₊ : ℝ) + 1) - s ≤ 1 := by linarith
        simpa [Nat.cast_add, Nat.cast_one] using h
      exact div_le_div_of_nonneg_right h_sub_le_one hs_nonneg
    exact ⟨ht_pos, hs_lt_t, h_ratio⟩
  · -- Part 2: rounding s downward to reciprocal mesh 1/(⌊s⁻¹⌋₊ + 1)
    set t : ℝ := (((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹ with ht_def
    have ht_pos : 0 < t := by
      rw [ht_def]
      have h_denom_pos : 0 < ((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ) := by
        have h_one_le : (1 : ℕ) ≤ ⌊s⁻¹⌋₊ + 1 := by omega
        exact mod_cast Nat.one_pos.trans_le h_one_le
      exact inv_pos.mpr h_denom_pos
    have ht_lt_s : t < s := by
      rw [ht_def]
      have h_cast : ((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ) = (⌊s⁻¹⌋₊ : ℝ) + 1 := by simp
      rw [h_cast]
      have h_lt : s⁻¹ < (⌊s⁻¹⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s⁻¹
      have hpos_u_add_one : 0 < (⌊s⁻¹⌋₊ : ℝ) + 1 := by
        have : 0 ≤ (⌊s⁻¹⌋₊ : ℝ) := Nat.cast_nonneg _
        positivity
      calc
        (((⌊s⁻¹⌋₊ : ℝ) + 1)⁻¹ : ℝ) = 1 / ((⌊s⁻¹⌋₊ : ℝ) + 1) := by rw [one_div]
        _ < 1 / (s⁻¹) := (one_div_lt_one_div hpos_u_add_one hs_pos').mpr h_lt
        _ = s := by field_simp
    have h_ratio : (s - t) / t ≤ s := by
      rw [ht_def]
      have h_cast : ((⌊s⁻¹⌋₊ + 1 : ℕ) : ℝ) = (⌊s⁻¹⌋₊ : ℝ) + 1 := by simp
      rw [h_cast]
      set u := ⌊s⁻¹⌋₊ with hu_def
      have hpos_u_add_one : 0 < (u : ℝ) + 1 := by
        have : 0 ≤ (u : ℝ) := Nat.cast_nonneg _
        positivity
      have h_floor_le : (u : ℝ) ≤ s⁻¹ := Nat.floor_le hsinv_nonneg
      have h_floor_le' : (u : ℝ) ≤ 1 / s := by
        simpa [one_div] using h_floor_le
      have h_mul : s * (u : ℝ) ≤ 1 := by
        simpa [mul_comm] using (le_div_iff₀ hs).mp h_floor_le'
      rw [← one_div ((u : ℝ) + 1)]
      have h_lhs_eq : (s - 1 / ((u : ℝ) + 1)) / (1 / ((u : ℝ) + 1)) = s * ((u : ℝ) + 1) - 1 := by
        field_simp [hpos_u_add_one.ne.symm]
      rw [h_lhs_eq]
      linarith
    exact ⟨ht_pos, ht_lt_s, h_ratio⟩

end EinsteinRelation.Correctors
