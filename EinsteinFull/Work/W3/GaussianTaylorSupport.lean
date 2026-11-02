import EinsteinFull.Frozen.ProfileTaylorCoefficient
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-! Taylor coefficients of the literal real Gaussian profile from Section 6. -/

namespace EinsteinFull

open scoped ContDiff

private lemma iteratedDeriv_id_mul_succ (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => y * f y) x =
      x * iteratedDeriv (n + 1) f x + (n + 1 : ℝ) * iteratedDeriv n f x := by
  induction n generalizing x with
  | zero =>
      simp only [iteratedDeriv_one, iteratedDeriv_zero, Nat.cast_zero, zero_add,
        one_mul]
      have h := ((hasDerivAt_id x).mul
        ((hf.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv
      change deriv (fun y => y * f y) x = 1 * f x + x * deriv f x at h
      rw [h]
      simp only [one_mul]
      ring
  | succ n ih =>
      have heq : iteratedDeriv (n + 1) (fun y => y * f y) =
          fun y => y * iteratedDeriv (n + 1) f y +
            (n + 1 : ℝ) * iteratedDeriv n f y := funext ih
      have hd (k : ℕ) : Differentiable ℝ (iteratedDeriv k f) :=
        hf.differentiable_iteratedDeriv k (by exact_mod_cast (ENat.coe_lt_top k))
      rw [iteratedDeriv_succ, heq]
      have h := (((hasDerivAt_id x).mul (hd (n + 1)).differentiableAt.hasDerivAt).add
        ((hd n).differentiableAt.hasDerivAt.const_mul (n + 1 : ℝ))).deriv
      change deriv (fun y => y * iteratedDeriv (n + 1) f y +
        (n + 1 : ℝ) * iteratedDeriv n f y) x =
          (1 * iteratedDeriv (n + 1) f x + x * deriv (iteratedDeriv (n + 1) f) x) +
            (n + 1 : ℝ) * deriv (iteratedDeriv n f) x at h
      rw [h]
      simp only [one_mul, ← iteratedDeriv_succ, Nat.cast_add, Nat.cast_one]
      ring

private lemma contDiff_gaussian_exp (γ : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => Real.exp (-γ * x ^ 2)) := by
  fun_prop

private lemma deriv_gaussian_exp (γ : ℝ) :
    deriv (fun x : ℝ => Real.exp (-γ * x ^ 2)) =
      fun x => (-2 * γ) * (x * Real.exp (-γ * x ^ 2)) := by
  funext x
  have h := (((hasDerivAt_id x).pow 2).const_mul (-γ)).exp.deriv
  change deriv (fun y => Real.exp (-γ * y ^ 2)) x =
    Real.exp (-γ * x ^ 2) * (-γ * (2 * x ^ (2 - 1) * 1)) at h
  rw [h]
  ring

private lemma iteratedDeriv_gaussian_exp_step (γ : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (fun x : ℝ => Real.exp (-γ * x ^ 2)) 0 =
      (-2 * γ) * (n + 1 : ℝ) *
        iteratedDeriv n (fun x : ℝ => Real.exp (-γ * x ^ 2)) 0 := by
  rw [show n + 2 = (n + 1) + 1 by omega, iteratedDeriv_succ', deriv_gaussian_exp,
    iteratedDeriv_const_mul_field (-2 * γ) (fun x : ℝ => x * Real.exp (-γ * x ^ 2)),
    iteratedDeriv_id_mul_succ _ (contDiff_gaussian_exp γ)]
  ring

private lemma iteratedDeriv_gaussian_exp_even (γ : ℝ) (n : ℕ) :
    iteratedDeriv (2 * n) (fun x : ℝ => Real.exp (-γ * x ^ 2)) 0 =
      ((2 * n).factorial : ℝ) * ((-γ) ^ n / (n.factorial : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega,
        iteratedDeriv_gaussian_exp_step, ih, pow_succ]
      rw [Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n),
        Nat.factorial_succ n]
      push_cast
      have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      have hn₁ : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

private lemma iteratedDeriv_sq_mul_succ_succ (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) :
    iteratedDeriv (n + 2) (fun x => x ^ 2 * f x) 0 =
      (n + 2 : ℝ) * (n + 1 : ℝ) * iteratedDeriv n f 0 := by
  have heq : (fun x => x ^ 2 * f x) = (fun x => x * (x * f x)) := by
    funext x
    ring
  rw [heq, show n + 2 = (n + 1) + 1 by omega,
    iteratedDeriv_id_mul_succ (fun x => x * f x)
      ((contDiff_id : ContDiff ℝ ∞ (fun x : ℝ => x)).mul hf),
    zero_mul, zero_add, iteratedDeriv_id_mul_succ _ hf, zero_mul, zero_add]
  push_cast
  ring

private lemma iteratedDeriv_gaussianProfile (u₀ u₂ γ : ℝ) (j : ℕ) :
    iteratedDeriv j (gaussianProfile u₀ u₂ γ) 0 =
      u₀ * iteratedDeriv j (fun x : ℝ => Real.exp (-γ * x ^ 2)) 0 +
        u₂ * iteratedDeriv j (fun x : ℝ => x ^ 2 * Real.exp (-γ * x ^ 2)) 0 := by
  have heq : gaussianProfile u₀ u₂ γ =
      (fun x => u₀ * Real.exp (-γ * x ^ 2)) +
        (fun x => u₂ * (x ^ 2 * Real.exp (-γ * x ^ 2))) := by
    funext x
    simp only [gaussianProfile, Pi.add_apply]
    ring
  rw [heq, iteratedDeriv_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const_mul_field u₀ (fun x : ℝ => Real.exp (-γ * x ^ 2)),
    iteratedDeriv_const_mul_field u₂ (fun x : ℝ => x ^ 2 * Real.exp (-γ * x ^ 2))]

/-- The constant Taylor coefficient retains the literal value of the profile at zero. -/
theorem profileTaylorCoefficient_zero (u₀ u₂ γ : ℝ) :
    profileTaylorCoefficient u₀ u₂ γ 0 = u₀ := by
  simp [profileTaylorCoefficient, gaussianProfile]

/-- Every odd Taylor coefficient of the frozen real Gaussian profile vanishes. -/
theorem profileTaylorCoefficient_odd (u₀ u₂ γ : ℝ) (n : ℕ) :
    profileTaylorCoefficient u₀ u₂ γ (2 * n + 1) = 0 := by
  have heq : (fun x => gaussianProfile u₀ u₂ γ (-x)) = gaussianProfile u₀ u₂ γ := by
    funext x
    simp only [gaussianProfile, neg_sq]
  have h := iteratedDeriv_comp_neg (2 * n + 1) (gaussianProfile u₀ u₂ γ) 0
  rw [heq] at h
  simp only [neg_zero, pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul,
    smul_eq_mul, neg_one_mul] at h
  unfold profileTaylorCoefficient
  have hz : iteratedDeriv (2 * n + 1) (gaussianProfile u₀ u₂ γ) 0 = 0 := by
    linarith only [h]
  rw [hz, zero_div]

/-- The even positive coefficients, with the factorial normalization of the manuscript. -/
theorem profileTaylorCoefficient_even_succ (u₀ u₂ γ : ℝ) (n : ℕ) :
    profileTaylorCoefficient u₀ u₂ γ (2 * (n + 1)) =
      u₀ * (-γ) ^ (n + 1) / ((n + 1).factorial : ℝ) +
        u₂ * (-γ) ^ n / (n.factorial : ℝ) := by
  unfold profileTaylorCoefficient
  rw [iteratedDeriv_gaussianProfile,
    show 2 * (n + 1) = 2 * n + 2 by omega,
    iteratedDeriv_sq_mul_succ_succ _ (contDiff_gaussian_exp γ),
    ← show 2 * (n + 1) = 2 * n + 2 by omega,
    iteratedDeriv_gaussian_exp_even, iteratedDeriv_gaussian_exp_even]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h₂n : ((2 * n).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (2 * n).factorial_ne_zero
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n), Nat.factorial_succ n]
  push_cast
  field_simp
  ring

/-- The even coefficient formula, including the constant coefficient without
interpreting a negative factorial or a negative exponent. -/
theorem profileTaylorCoefficient_even (u₀ u₂ γ : ℝ) (n : ℕ) :
    profileTaylorCoefficient u₀ u₂ γ (2 * n) =
      u₀ * (-γ) ^ n / (n.factorial : ℝ) +
        if n = 0 then 0 else u₂ * (-γ) ^ (n - 1) / ((n - 1).factorial : ℝ) := by
  cases n with
  | zero => simp [profileTaylorCoefficient_zero]
  | succ n =>
      simpa only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] using
        profileTaylorCoefficient_even_succ u₀ u₂ γ n

/-- The manuscript formula `h_(2n)` at positive `n`, for arbitrary real parameters. -/
theorem profileTaylorCoefficient_even_of_pos (u₀ u₂ γ : ℝ) {n : ℕ} (hn : 0 < n) :
    profileTaylorCoefficient u₀ u₂ γ (2 * n) =
      u₀ * (-γ) ^ n / (n.factorial : ℝ) +
        u₂ * (-γ) ^ (n - 1) / ((n - 1).factorial : ℝ) := by
  rw [profileTaylorCoefficient_even, if_neg (Nat.ne_of_gt hn)]

/-- A closed formula at every degree for the actual derivative-defined coefficient. -/
theorem profileTaylorCoefficient_eq (u₀ u₂ γ : ℝ) (j : ℕ) :
    profileTaylorCoefficient u₀ u₂ γ j =
      if j % 2 = 0 then
        u₀ * (-γ) ^ (j / 2) / ((j / 2).factorial : ℝ) +
          (if j / 2 = 0 then 0
           else u₂ * (-γ) ^ (j / 2 - 1) / ((j / 2 - 1).factorial : ℝ))
      else 0 := by
  by_cases h : j % 2 = 0
  · rw [if_pos h]
    have hj : 2 * (j / 2) = j := by omega
    simpa only [hj] using profileTaylorCoefficient_even u₀ u₂ γ (j / 2)
  · rw [if_neg h]
    have hj : j = 2 * (j / 2) + 1 := by omega
    rw [hj, profileTaylorCoefficient_odd]

end EinsteinFull
