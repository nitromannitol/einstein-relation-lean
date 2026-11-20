import EinsteinFull.External.DFGW.DynkinDyadicMaximal

/-! # Dyadic time grids and unit blocks

Each dyadic point on an integer-length interval is a dyadic point in one of its unit blocks.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

/-- A dyadic point on `[0,n]` is contained in a unit block with index at most `n`. -/
theorem dyadicGridTime_nat_eq_block (n r j : ℕ) (hj : j ≤ 2 ^ r) :
    ∃ k l : ℕ, k ≤ n ∧ l ≤ 2 ^ r ∧
      dyadicGridTime (n : ℝ≥0) r j = (k : ℝ≥0) + dyadicGridTime 1 r l := by
  let D : ℕ := 2 ^ r
  have hD : 0 < D := by dsimp only [D]; positivity
  let k := (n * j) / D
  let l := (n * j) % D
  have hprod : n * j ≤ n * D := Nat.mul_le_mul_left n hj
  have hk : k ≤ n := Nat.div_le_of_le_mul (by simpa only [mul_comm] using hprod)
  have hl : l ≤ D := (Nat.mod_lt _ hD).le
  refine ⟨k, l, hk, hl, ?_⟩
  apply NNReal.eq
  simp only [dyadicGridTime, nsmul_eq_mul, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_one]
  have hdiv : l + D * k = n * j := by
    dsimp only [l, k]
    exact Nat.mod_add_div (n * j) D
  have hdivR : (l : ℝ) + (D : ℝ) * (k : ℝ) = (n : ℝ) * (j : ℝ) := by exact_mod_cast hdiv
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  change (j : ℝ) * ((n : ℝ) / (D : ℝ)) = (k : ℝ) + (l : ℝ) * (1 / (D : ℝ))
  field_simp
  nlinarith

end EinsteinFull.External.DFGW
