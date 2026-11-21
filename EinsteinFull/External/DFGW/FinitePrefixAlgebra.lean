import EinsteinFull.External.DFGW.WeightedVectorArray

/-! # Algebra of finite prefix sums

Squares of sums of prefix-truncated terms expand into pairwise cross-products over the
intersection of the prefixes.
-/

open scoped BigOperators

namespace EinsteinFull.External.DFGW

/-- The square of a sum of prefix-truncated terms is the sum of pairwise cross-products. -/
theorem sum_sq_prefix_sum {J : Type*} (s : Finset J) (K : ℕ) (m : J → ℕ)
    (a : J → ℕ → ℝ) :
    ∑ k ∈ Finset.range K, (∑ j ∈ s, if k < m j then a j k else 0) ^ 2 =
      ∑ j ∈ s, ∑ l ∈ s, ∑ k ∈ Finset.range K,
        if k < m j ∧ k < m l then a j k * a l k else 0 := by
  classical
  calc
    _ = ∑ k ∈ Finset.range K, ∑ j ∈ s, ∑ l ∈ s,
        if k < m j ∧ k < m l then a j k * a l k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hj' : k < m j <;> by_cases hl' : k < m l <;> simp [hj', hl']
    _ = _ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j hj; rw [Finset.sum_comm]

/-- If all prefixes lie inside the summation range, their intersections determine the
cross-product ranges. -/
theorem sum_sq_prefix_sum_eq_sum_min {J : Type*} (s : Finset J) (K : ℕ) (m : J → ℕ)
    (a : J → ℕ → ℝ) (hm : ∀ j ∈ s, m j ≤ K) :
    ∑ k ∈ Finset.range K, (∑ j ∈ s, if k < m j then a j k else 0) ^ 2 =
      ∑ j ∈ s, ∑ l ∈ s, ∑ k ∈ Finset.range (min (m j) (m l)), a j k * a l k := by
  classical
  rw [sum_sq_prefix_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range K).filter (fun k => k < m j ∧ k < m l) =
      Finset.range (min (m j) (m l)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lt_of_lt_of_le h.1 (hm j hj), h⟩
  rw [hfilter]

end EinsteinFull.External.DFGW
