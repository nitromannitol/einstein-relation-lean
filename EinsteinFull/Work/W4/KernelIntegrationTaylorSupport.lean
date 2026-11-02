import EinsteinFull.Work.W4.KernelCauchyCoefficientSupport
import Mathlib.Analysis.Calculus.Taylor

/-! Signed Taylor remainders and shifted Cauchy estimates for the actual
profile-subtracted kernel in Proposition 6.7. -/

open Set

namespace EinsteinFull

private theorem taylorWithinEval_eq_sum (f : ℝ → ℝ) (d : ℕ) {s : ℝ}
    (hs : 0 < s) (hf : ContDiff ℝ ((d + 1 : ℕ) : WithTop ℕ∞) f) (x : ℝ) :
    taylorWithinEval f d (Icc 0 s) 0 x =
      ∑ j : Fin (d + 1), iteratedDeriv j.val f 0 / (j.val.factorial : ℝ) * x ^ j.val := by
  rw [taylor_within_apply, Fin.sum_univ_eq_sum_range
    (fun j => iteratedDeriv j f 0 / (j.factorial : ℝ) * x ^ j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_eq_iteratedDeriv (n := j) (uniqueDiffOn_Icc hs)
    (hf.of_le (by exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hj))).contDiffAt
      (by simp [hs.le])]
  simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem taylor_remainder_nonneg {f : ℝ → ℝ} (d : ℕ) {s M x : ℝ}
    (hs : 0 < s) (hf : ContDiff ℝ ((d + 1 : ℕ) : WithTop ℕ∞) f)
    (hx : x ∈ Icc 0 s)
    (hb : ∀ y ∈ Icc (0 : ℝ) s, ‖iteratedDeriv (d + 1) f y‖ ≤ M) :
    |f x - ∑ j : Fin (d + 1), iteratedDeriv j.val f 0 / (j.val.factorial : ℝ) * x ^ j.val| ≤
      M * x ^ (d + 1) / (d.factorial : ℝ) := by
  have h := taylor_mean_remainder_bound hs.le hf.contDiffOn hx (C := M) (by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs) hf.contDiffAt hy]
    exact hb y hy)
  rwa [taylorWithinEval_eq_sum f d hs hf, sub_zero, Real.norm_eq_abs] at h

/-- Taylor's bound on a symmetric real interval with literal iterated
derivatives and signed powers. The negative-force case is proved by reflection. -/
theorem real_taylor_remainder_bound_signed {f : ℝ → ℝ} (d : ℕ) {s M : ℝ}
    (hs : 0 < s) (hf : ContDiff ℝ ((d + 1 : ℕ) : WithTop ℕ∞) f)
    (hb : ∀ y : ℝ, |y| ≤ s → ‖iteratedDeriv (d + 1) f y‖ ≤ M)
    {lam : ℝ} (hlam : |lam| ≤ s) :
    |f lam - ∑ j : Fin (d + 1), iteratedDeriv j.val f 0 /
      (j.val.factorial : ℝ) * lam ^ j.val| ≤
        M * |lam| ^ (d + 1) / (d.factorial : ℝ) := by
  by_cases hl : 0 ≤ lam
  · rw [abs_of_nonneg hl] at hlam ⊢
    exact taylor_remainder_nonneg d hs hf ⟨hl, hlam⟩
      (fun y hy => hb y (by simpa only [abs_of_nonneg hy.1] using hy.2))
  · have hl : lam < 0 := lt_of_not_ge hl
    have hg : ContDiff ℝ ((d + 1 : ℕ) : WithTop ℕ∞) (fun x => f (-x)) := hf.comp contDiff_neg
    have h := taylor_remainder_nonneg d hs hg
      (show -lam ∈ Icc (0 : ℝ) s by rw [abs_of_neg hl] at hlam; exact ⟨by linarith, hlam⟩)
      (M := M) (by
        intro y hy
        rw [iteratedDeriv_comp_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact hb (-y) (by simpa only [abs_neg, abs_of_nonneg hy.1] using hy.2))
    simp only [neg_neg, iteratedDeriv_comp_neg, neg_zero, smul_eq_mul] at h
    have he : (∑ j : Fin (d + 1),
        ((-1 : ℝ) ^ j.val * iteratedDeriv j.val f 0) / (j.val.factorial : ℝ) * (-lam) ^ j.val) =
        ∑ j : Fin (d + 1), iteratedDeriv j.val f 0 / (j.val.factorial : ℝ) * lam ^ j.val := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (iteratedDeriv j.val f 0 / (j.val.factorial : ℝ)) *
            ((-1 : ℝ) ^ j.val * (-lam) ^ j.val) := by ring
        _ = (iteratedDeriv j.val f 0 / (j.val.factorial : ℝ)) *
            ((-1 : ℝ) * (-lam)) ^ j.val := by rw [mul_pow]
        _ = _ := by rw [neg_one_mul, neg_neg]
    rw [he] at h
    simpa only [abs_of_neg hl] using h

private theorem real_derivative_le_cauchy {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (j : ℕ) (x : ℝ) {R M : ℝ} (hR : 0 < R)
    (hb : ∀ z ∈ Metric.sphere (x : ℂ) R, ‖f z‖ ≤ M) :
    ‖iteratedDeriv j (fun y : ℝ => (f (y : ℂ)).re) x‖ ≤
      (j.factorial : ℝ) * M / R ^ j := by
  rw [iteratedDeriv_re_of_entire hf, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans
    (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR
      (hf.differentiableOn.diffContOnCl) hb)

/-- Cauchy bounds at every real force in the smaller scaled disc, derived
from the actual fixed-disc profile hypothesis. The decay at order d+1 is
exactly t^(-1/2-alpha), as needed for the small-time integral. -/
theorem kernel_remainder_shifted_derivative_bound (d j : ℕ) (α C : ℝ) (hC : 0 < C)
    (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
    (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hb : ∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
      ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
        C * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2))
    {t x : ℝ} (ht : 1 ≤ t) (hx : |x| * Real.sqrt t ≤ 1) :
    ‖iteratedDeriv j (fun y : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (y : ℂ)).re) x‖ ≤
      (j.factorial : ℝ) * (C * Real.exp (9 * C)) *
        t ^ (-1 - ((d : ℝ) - j) / 2 - α) := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht₀
  have H := real_derivative_le_cauchy
    (differentiable_kernelProfileRemainder d u₀ u₂ γ K t (hK t ht₀.le)) j x
    (one_div_pos.mpr hs) (M := C * t ^ (-1 - (d : ℝ) / 2 - α) * Real.exp (9 * C)) (by
      intro z hz
      have hz' : ‖z - (x : ℂ)‖ = 1 / Real.sqrt t := by
        simpa only [Metric.mem_sphere, dist_eq_norm] using hz
      have hscaled : ‖z‖ * Real.sqrt t ≤ 2 := by
        have hn : ‖z‖ ≤ ‖z - (x : ℂ)‖ + |x| := by
          simpa only [Complex.norm_real, Real.norm_eq_abs, add_comm] using
            norm_le_norm_add_norm_sub' z (x : ℂ)
        have hm := mul_le_mul_of_nonneg_right hn hs.le
        rw [add_mul, hz', one_div_mul_cancel hs.ne'] at hm
        linarith only [hm, hx]
      have h := hb t ht z hscaled
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ ‖z‖ * Real.sqrt t := by positivity
      have hsq : (1 + ‖z‖ * Real.sqrt t) ^ 2 ≤ 9 := by nlinarith only [hn, hscaled]
      exact (mul_le_mul_of_nonneg_left hsq hC.le).trans_eq (mul_comm _ _))
  apply H.trans_eq
  rw [one_div_pow, div_div_eq_mul_div, div_one,
    Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht₀.le]
  calc
    _ = (j.factorial : ℝ) * (C * Real.exp (9 * C)) *
        (t ^ (-1 - (d : ℝ) / 2 - α) * t ^ ((1 / 2 : ℝ) * j)) := by ring
    _ = _ := by rw [← Real.rpow_add ht₀]; congr 2; ring

/-- The actual Taylor error on the fixed scaled disc, for either force sign.
No derivative bound is assumed: the preceding shifted Cauchy estimate supplies it. -/
theorem kernel_remainder_taylor_large_bound (d : ℕ) (α C : ℝ) (hC : 0 < C)
    (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
    (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hb : ∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
      ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
        C * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2))
    {t lam : ℝ} (ht : 1 ≤ t) (hlam : 0 < |lam|)
    (hscaled : |lam| * Real.sqrt t ≤ 1) :
    |(kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re -
      ∑ j : Fin (d + 1),
        (iteratedDeriv j.val (fun y : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (y : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) * lam ^ j.val| ≤
      ((d + 1 : ℕ) : ℝ) * (C * Real.exp (9 * C)) *
        |lam| ^ (d + 1) * t ^ (-1 / 2 - α) := by
  have hf : ContDiff ℝ ((d + 1 : ℕ) : WithTop ℕ∞) (fun y : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (y : ℂ)).re) :=
    (differentiable_kernelProfileRemainder d u₀ u₂ γ K t
      (hK t (zero_le_one.trans ht))).contDiff.real_of_complex
  have H := real_taylor_remainder_bound_signed d hlam hf (s := |lam|)
    (M := ((d + 1).factorial : ℝ) * (C * Real.exp (9 * C)) * t ^ (-1 / 2 - α))
    (by
      intro y hy
      have h := kernel_remainder_shifted_derivative_bound d (d + 1) α C hC
        u₀ u₂ γ K hK hb ht
        ((mul_le_mul_of_nonneg_right hy (Real.sqrt_nonneg t)).trans hscaled)
      have he : -1 - ((d : ℝ) - ((d + 1 : ℕ) : ℝ)) / 2 - α = -1 / 2 - α := by
        push_cast
        ring
      simpa only [he] using h) le_rfl
  apply H.trans_eq
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

/-- Shifted Cauchy control on the bounded initial time interval uses precisely
the source radius-two bound for K, before the profile cutoff. -/
theorem kernel_remainder_initial_shifted_derivative_bound (d j : ℕ) (u₀ u₂ γ C : ℝ)
    (K : ℝ → ℂ → ℂ) (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C)
    {t x : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1) (hx : |x| ≤ 1) :
    ‖iteratedDeriv j (fun y : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (y : ℂ)).re) x‖ ≤
        (j.factorial : ℝ) * C := by
  have he : kernelProfileRemainder d u₀ u₂ γ K t = K t := by
    funext z
    simp only [kernelProfileRemainder, if_neg (not_le.mpr ht₁), sub_zero]
  rw [he]
  simpa only [one_pow, div_one] using real_derivative_le_cauchy (hK t ht) j x zero_lt_one
    (M := C) (by
      intro z hz
      have hz' : ‖z - (x : ℂ)‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_eq_norm] using hz
      apply hb t ht ht₁.le z
      have hn := norm_le_norm_add_norm_sub' z (x : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, hz'] at hn
      linarith only [hn, hx])

/-- The literal initial-interval Taylor error is O(C*s^(d+1)), uniformly in
the amplitudes, rate and actual kernel, for both force signs. -/
theorem kernel_remainder_taylor_initial_bound (d : ℕ) (u₀ u₂ γ C : ℝ)
    (K : ℝ → ℂ → ℂ) (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C)
    {t lam : ℝ} (ht : 0 ≤ t) (ht₁ : t < 1) (hlam : 0 < |lam|) (hs : |lam| ≤ 1) :
    |(kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re -
      ∑ j : Fin (d + 1),
        (iteratedDeriv j.val (fun y : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (y : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) * lam ^ j.val| ≤
      ((d + 1 : ℕ) : ℝ) * C * |lam| ^ (d + 1) := by
  have hf : ContDiff ℝ ((d + 1 : ℕ) : WithTop ℕ∞) (fun y : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (y : ℂ)).re) :=
    (differentiable_kernelProfileRemainder d u₀ u₂ γ K t (hK t ht)).contDiff.real_of_complex
  have H := real_taylor_remainder_bound_signed d hlam hf (s := |lam|)
    (M := ((d + 1).factorial : ℝ) * C)
    (fun y hy => kernel_remainder_initial_shifted_derivative_bound d (d + 1)
      u₀ u₂ γ C K hK hb ht ht₁ (hy.trans hs)) le_rfl
  apply H.trans_eq
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

end EinsteinFull
