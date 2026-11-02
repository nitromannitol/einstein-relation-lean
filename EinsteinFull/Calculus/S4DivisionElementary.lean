import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Frozen.CriticalKernelTerm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary inequalities for the expansion modulus

With `L = log (1/s) ≥ 1` and `M = expansionModulus s = exp (-√L)` on `0 < s ≤ exp (-1)`:

* `s ≤ M`;
* `s (1 + L) ≤ 4 M`;
* `s (1 + L)² ≤ 16 M`;
* the critical kernel term satisfies `|T| ≤ s^d (1 + L)`.
-/

open Real

namespace EinsteinFull

theorem log_one_div_ge_one {s : ℝ} (hs : 0 < s) (h : s ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / s) := by
  have h1 : Real.log s ≤ -1 := by
    have := Real.log_le_log hs h
    rwa [Real.log_exp] at this
  rw [one_div, Real.log_inv]
  linarith

theorem eq_exp_neg_log_one_div {s : ℝ} (hs : 0 < s) :
    s = Real.exp (-Real.log (1 / s)) := by
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log hs]

theorem exp_neg_sq_le (r : ℝ) (hr : 1 ≤ r) : Real.exp (-(r * r)) ≤ Real.exp (-r) :=
  Real.exp_le_exp.2 (by nlinarith)

theorem aux_one_add_sq (r : ℝ) :
    (1 + r * r) * Real.exp (-(r * r)) ≤ 4 * Real.exp (-r) := by
  have hexp := Real.add_one_le_exp (r * r - r)
  have h4 : 1 + r * r ≤ 4 * Real.exp (r * r - r) := by
    nlinarith [hexp, sq_nonneg (3 * r - 2)]
  have e1 : Real.exp (-(r * r)) = Real.exp (-r) * Real.exp (-(r * r - r)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(r * r - r)) * Real.exp (r * r - r) = 1 := by
    rw [← Real.exp_add]; simp
  rw [e1]
  calc (1 + r * r) * (Real.exp (-r) * Real.exp (-(r * r - r)))
      = Real.exp (-r) * ((1 + r * r) * Real.exp (-(r * r - r))) := by ring
    _ ≤ Real.exp (-r) * (4 * Real.exp (r * r - r) * Real.exp (-(r * r - r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = 4 * Real.exp (-r) := by
        rw [mul_assoc, mul_comm (Real.exp (r * r - r)), e2]; ring

theorem aux_one_add_sq_sq (r : ℝ) (hr : 1 ≤ r) :
    (1 + r * r) ^ 2 * Real.exp (-(r * r)) ≤ 16 * Real.exp (-r) := by
  have hx : 0 ≤ r * r - r := by nlinarith
  have hexp := Real.quadratic_le_exp_of_nonneg hx
  have hpoly : (1 + r * r) ^ 2 ≤ 16 * (1 + (r * r - r) + (r * r - r) ^ 2 / 2) := by
    nlinarith [sq_nonneg (7 * r ^ 2 - 8 * r), sq_nonneg (45 * r - 28)]
  have h4 : (1 + r * r) ^ 2 ≤ 16 * Real.exp (r * r - r) := by linarith [hexp]
  have e1 : Real.exp (-(r * r)) = Real.exp (-r) * Real.exp (-(r * r - r)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(r * r - r)) * Real.exp (r * r - r) = 1 := by
    rw [← Real.exp_add]; simp
  rw [e1]
  calc (1 + r * r) ^ 2 * (Real.exp (-r) * Real.exp (-(r * r - r)))
      = Real.exp (-r) * ((1 + r * r) ^ 2 * Real.exp (-(r * r - r))) := by ring
    _ ≤ Real.exp (-r) * (16 * Real.exp (r * r - r) * Real.exp (-(r * r - r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = 16 * Real.exp (-r) := by
        rw [mul_assoc, mul_comm (Real.exp (r * r - r)), e2]; ring

/-- Data `r = √L ≥ 1`, `L = r * r`, `s = exp (-L)`. -/
theorem modulus_data {s : ℝ} (hs : 0 < s) (h : s ≤ Real.exp (-1)) :
    ∃ r : ℝ, 1 ≤ r ∧ s = Real.exp (-(r * r)) ∧ Real.log (1 / s) = r * r ∧
      expansionModulus s hs h = Real.exp (-r) := by
  have hL := log_one_div_ge_one hs h
  have hsq : Real.sqrt (Real.log (1 / s)) * Real.sqrt (Real.log (1 / s)) = Real.log (1 / s) :=
    Real.mul_self_sqrt (by linarith)
  have hr : 1 ≤ Real.sqrt (Real.log (1 / s)) := Real.one_le_sqrt.2 hL
  refine ⟨Real.sqrt (Real.log (1 / s)), hr, ?_, hsq.symm, rfl⟩
  rw [hsq]
  exact eq_exp_neg_log_one_div hs

theorem le_expansionModulus {s : ℝ} (hs : 0 < s) (h : s ≤ Real.exp (-1)) :
    s ≤ expansionModulus s hs h := by
  obtain ⟨r, hr, hsr, -, hM⟩ := modulus_data hs h
  rw [hM, hsr]
  exact exp_neg_sq_le r hr

theorem mul_one_add_log_le {s : ℝ} (hs : 0 < s) (h : s ≤ Real.exp (-1)) :
    s * (1 + Real.log (1 / s)) ≤ 4 * expansionModulus s hs h := by
  obtain ⟨r, hr, hsr, hL, hM⟩ := modulus_data hs h
  rw [hM, hL, hsr]
  have := aux_one_add_sq r
  linarith

theorem mul_one_add_log_sq_le {s : ℝ} (hs : 0 < s) (h : s ≤ Real.exp (-1)) :
    s * (1 + Real.log (1 / s)) ^ 2 ≤ 16 * expansionModulus s hs h := by
  obtain ⟨r, hr, hsr, hL, hM⟩ := modulus_data hs h
  rw [hM, hL, hsr]
  have := aux_one_add_sq_sq r hr
  linarith

theorem abs_criticalKernelTerm_le (d : ℕ) {lam : ℝ} (hlam : lam ≠ 0)
    (h : |lam| ≤ Real.exp (-1)) :
    |criticalKernelTerm d lam hlam| ≤ |lam| ^ d * (1 + Real.log (1 / |lam|)) := by
  have hL := log_one_div_ge_one (abs_pos.2 hlam) h
  have hpow : 0 ≤ |lam| ^ d := pow_nonneg (abs_nonneg _) _
  unfold criticalKernelTerm
  split_ifs with hd
  · rw [abs_mul, abs_pow, abs_of_nonneg (by linarith : 0 ≤ Real.log (1 / |lam|))]
    exact mul_le_mul_of_nonneg_left (by linarith) hpow
  · rw [abs_pow, abs_abs]
    nlinarith

end EinsteinFull
