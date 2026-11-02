import EinsteinFull.Calculus.C6FluxActualRecoveryBudget

namespace EinsteinFull.Blueprint

theorem c6_order_sum_positive_product_majorant (F : ℕ → ℝ) :
    ∃ A B : ℕ → ℝ, (∀ k, 0 < A k) ∧ (∀ q, 0 < B q) ∧
      ∀ k q : ℕ, max 1 (F (k + q)) ≤ A k * B q := by
  let P : ℕ → ℝ := fun n => 1 + ∑ j ∈ Finset.range (2 * n + 1), max 1 (F j)
  have hP : ∀ n, 1 ≤ P n := by
    intro n
    dsimp [P]
    have : 0 ≤ ∑ j ∈ Finset.range (2 * n + 1), max 1 (F j) :=
      Finset.sum_nonneg (fun j _ => le_trans (by norm_num) (le_max_left _ _))
    linarith
  have hbound : ∀ n j, j ≤ 2 * n → max 1 (F j) ≤ P n := by
    intro n j hj
    have hmem : j ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
    have hs := Finset.single_le_sum (fun i _ => le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 (F i))) hmem
    dsimp [P]
    linarith
  refine ⟨P, P, fun n => lt_of_lt_of_le (by norm_num) (hP n),
    fun n => lt_of_lt_of_le (by norm_num) (hP n), ?_⟩
  intro k q
  rcases le_total q k with h | h
  · have hb := hbound k (k + q) (by omega)
    have hm : P k ≤ P k * P q := by nlinarith [hP k, hP q]
    exact le_trans hb hm
  · have hb := hbound q (k + q) (by omega)
    have hm : P q ≤ P k * P q := by nlinarith [hP k, hP q]
    exact le_trans hb hm

end EinsteinFull.Blueprint
