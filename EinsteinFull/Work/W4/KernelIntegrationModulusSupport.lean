import EinsteinFull.Work.W4.KernelIntegrationTailSupport
import EinsteinFull.Frozen.ExpansionModulus

/-! Explicit structural thresholds for the common expansion modulus. -/

namespace EinsteinFull

/-- A fixed power of the force absorbs every fixed exponential in the square
root of its logarithm. The threshold is chosen before the force. -/
theorem exists_force_threshold_rpow_exp_sqrt_log_bound (α A k : ℝ)
    (hα : 0 < α) (hA : 0 ≤ A) (hk : 0 ≤ k) :
    ∃ s_star : ℝ, 0 < s_star ∧ s_star ≤ Real.exp (-1) ∧
      ∀ s : ℝ, 0 < s → s ≤ s_star →
      s ^ (2 * α) * Real.exp (A * Real.sqrt (Real.log (1 / s))) ≤
        Real.exp (-k * Real.sqrt (Real.log (1 / s))) := by
  let q : ℝ := (A + k) / (2 * α)
  let M : ℝ := max 1 (q ^ 2)
  have hM : 1 ≤ M := le_max_left _ _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  refine ⟨Real.exp (-M), Real.exp_pos _,
    Real.exp_le_exp.mpr (neg_le_neg hM), ?_⟩
  intro s hs hss
  have hlog := Real.log_le_log hs hss
  rw [Real.log_exp] at hlog
  have hL : M ≤ Real.log (1 / s) := by
    rw [one_div, Real.log_inv]
    linarith
  have hL₀ : 0 ≤ Real.log (1 / s) := zero_le_one.trans (hM.trans hL)
  have hsqrt : q ≤ Real.sqrt (Real.log (1 / s)) :=
    (Real.le_sqrt hq hL₀).mpr ((le_max_right _ _).trans hL)
  have hlinear : A + k ≤ 2 * α * Real.sqrt (Real.log (1 / s)) :=
    (div_le_iff₀ (by positivity : 0 < 2 * α)).mp hsqrt |>.trans_eq (mul_comm _ _)
  have hmul := mul_le_mul_of_nonneg_right hlinear
    (Real.sqrt_nonneg (Real.log (1 / s)))
  rw [Real.rpow_def_of_pos hs, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : Real.log s = -Real.log (1 / s) := by rw [one_div, Real.log_inv, neg_neg]
  rw [he]
  have heq : 2 * α * Real.sqrt (Real.log (1 / s)) * Real.sqrt (Real.log (1 / s)) =
      2 * α * Real.log (1 / s) := by
    calc
      _ = 2 * α * Real.sqrt (Real.log (1 / s)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hL₀]
  rw [heq] at hmul
  linarith only [hmul]

/-- The model's extra ordinary power is bounded by the exact frozen modulus
on the full prescribed force range. -/
theorem force_le_expansionModulus (s : ℝ) (hs : 0 < s)
    (hsmall : s ≤ Real.exp (-1)) : s ≤ expansionModulus s hs hsmall := by
  have hL : 1 ≤ Real.log (1 / s) := by
    have h := Real.log_le_log hs hsmall
    rw [Real.log_exp] at h
    rw [one_div, Real.log_inv]
    linarith
  have hsqrt : Real.sqrt (Real.log (1 / s)) ≤ Real.log (1 / s) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨zero_le_one.trans hL, ?_⟩
    nlinarith only [hL]
  change s ≤ Real.exp (-Real.sqrt (Real.log (1 / s)))
  calc
    s = Real.exp (Real.log s) := (Real.exp_log hs).symm
    _ ≤ Real.exp (-Real.sqrt (Real.log (1 / s))) := by
      apply Real.exp_le_exp.mpr
      have he : Real.log s = -Real.log (1 / s) := by rw [one_div, Real.log_inv, neg_neg]
      linarith only [hsqrt, he]

/-- Uniform model errors of order d+1 fit the requested critical-order error. -/
theorem force_pow_succ_le_expansionModulus (d : ℕ) (s : ℝ) (hs : 0 < s)
    (hsmall : s ≤ Real.exp (-1)) :
    s ^ (d + 1) ≤ s ^ d * expansionModulus s hs hsmall := by
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left (force_le_expansionModulus s hs hsmall) (by positivity)

end EinsteinFull
