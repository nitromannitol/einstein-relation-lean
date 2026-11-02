import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators

noncomputable section
namespace EinsteinFull.Calculus

/-- The literal scalar factors in a geometric Moser iteration have a uniform product bound. -/
theorem c17_moser_geometric_product_bound (A b c p : ℝ)
    (hA : 1 ≤ A) (hb : 1 < b) (hc : 1 < c) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∏ n ∈ Finset.range N,
        Real.rpow (A * Real.rpow b (n : ℝ))
          (1 / (p * Real.rpow c (n : ℝ)))) ≤ C := by
  have hA0 : 0 < A := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  let q : ℝ := c⁻¹
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; exact inv_lt_one₀ hc0 |>.2 hc
  have hs0 : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hs1 : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1))
  let f : ℕ → ℝ := fun n => (Real.log A / p) * q ^ n +
    (Real.log b / p) * ((n : ℝ) * q ^ n)
  have hf : Summable f := (hs0.mul_left _).add (hs1.mul_left _)
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    have ha : 0 ≤ Real.log A := Real.log_nonneg hA
    have hb' : 0 ≤ Real.log b := Real.log_nonneg hb.le
    positivity
  have hlog : ∀ n : ℕ,
      Real.log (Real.rpow (A * Real.rpow b (n : ℝ))
        (1 / (p * Real.rpow c (n : ℝ)))) = f n := by
    intro n
    simp only [Real.rpow_eq_pow]
    rw [Real.log_rpow (x := A * b ^ (n : ℝ)) (by positivity) (1 / (p * c ^ (n : ℝ))),
      Real.log_mul (ne_of_gt hA0) (by positivity : b ^ (n : ℝ) ≠ 0),
      Real.log_rpow hb0 (n : ℝ), Real.rpow_natCast]
    dsimp [f, q]
    rw [inv_pow]
    field_simp
  refine ⟨Real.exp (∑' n, f n), Real.exp_pos _, ?_⟩
  intro N
  have hfactor : ∀ n : ℕ, 0 < Real.rpow (A * Real.rpow b (n : ℝ))
      (1 / (p * Real.rpow c (n : ℝ))) := by
    intro n
    exact Real.rpow_pos_of_pos (mul_pos hA0 (Real.rpow_pos_of_pos hb0 _)) _
  calc
    (∏ n ∈ Finset.range N, Real.rpow (A * Real.rpow b (n : ℝ))
        (1 / (p * Real.rpow c (n : ℝ)))) =
        Real.exp (∑ n ∈ Finset.range N, f n) := by
          rw [Real.exp_sum]
          apply Finset.prod_congr rfl
          intro n hn
          rw [← hlog n, Real.exp_log (hfactor n)]
    _ ≤ Real.exp (∑' n, f n) := Real.exp_le_exp.mpr (hf.sum_le_tsum _ (fun n _ => hf0 n))

/-- A positive sequence satisfying the one-step Moser recurrence inherits the uniform bound. -/
theorem c17_moser_geometric_iteration_bound (A b c p : ℝ)
    (hA : 1 ≤ A) (hb : 1 < b) (hc : 1 < c) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ → ℝ, (∀ n, 0 ≤ X n) →
      (∀ n, X (n + 1) ≤ Real.rpow (A * Real.rpow b (n : ℝ))
        (1 / (p * Real.rpow c (n : ℝ))) * X n) →
      ∀ N, X N ≤ C * X 0 := by
  obtain ⟨C, hC, hprod⟩ := c17_moser_geometric_product_bound A b c p hA hb hc hp
  refine ⟨C, hC, ?_⟩
  intro X hX hstep N
  have hiter : ∀ N : ℕ, X N ≤
      (∏ n ∈ Finset.range N, Real.rpow (A * Real.rpow b (n : ℝ))
        (1 / (p * Real.rpow c (n : ℝ)))) * X 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.prod_range_succ]
      have hA0 : 0 < A := by linarith
      have hb0 : 0 < b := by linarith
      have hpos : 0 ≤ Real.rpow (A * Real.rpow b (N : ℝ))
          (1 / (p * Real.rpow c (N : ℝ))) := Real.rpow_nonneg (mul_nonneg hA0.le (Real.rpow_nonneg hb0.le _)) _
      calc
        X (N + 1) ≤ _ := hstep N
        _ ≤ _ := mul_le_mul_of_nonneg_left ih hpos
        _ = _ := by ring
  exact (hiter N).trans (mul_le_mul_of_nonneg_right (hprod N) (hX 0))

end EinsteinFull.Calculus
