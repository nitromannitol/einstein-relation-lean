import EinsteinFull.Work.W4.KernelIntegrationProof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Quantitative time integration of the actual Cauchy and signed Taylor
estimates, with the force cutoff and the growing logarithmic window. -/

open MeasureTheory Set

namespace EinsteinFull

/-- The force cutoff preserves the literal real-power normalization. -/
theorem force_cutoff_rpow {s : ℝ} (hs : 0 < s) (p : ℝ) :
    (1 / s ^ 2) ^ p = s ^ (-2 * p) := by
  rw [Real.div_rpow zero_le_one (sq_nonneg s), Real.one_rpow,
    ← Real.rpow_natCast_mul hs.le, one_div, ← Real.rpow_neg hs.le]
  congr 1
  ring

/-- Integrating a decaying power from the actual force cutoff. -/
theorem integral_force_cutoff_power {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    (∫ t in Ici (1 / s ^ 2), t ^ (-1 - β)) = s ^ (2 * β) / β := by
  rw [integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith)
    (by positivity : 0 < 1 / s ^ 2), force_cutoff_rpow hs]
  have he : -2 * (-1 - β + 1) = 2 * β := by ring
  rw [he, show -1 - β + 1 = -β by ring, div_neg, neg_div, neg_neg]

/-- A bounded interval power integral keeps the alpha gain. The source upper
bound alpha<=1/4 supplies a uniform denominator at least 1/4. -/
theorem integral_taylor_time_power {α S : ℝ} (hα : 0 < α) (hα' : α ≤ 1 / 4)
    (hS : 1 ≤ S) :
    (∫ t in Icc (1 : ℝ) S, t ^ (-1 / 2 - α)) ≤ 4 * S ^ (1 / 2 - α) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hS,
    integral_rpow (Or.inl (by linarith : -1 < -1 / 2 - α))]
  rw [show -1 / 2 - α + 1 = 1 / 2 - α by ring, Real.one_rpow]
  have hq : 0 < 1 / 2 - α := by linarith
  apply (div_le_iff₀ hq).mpr
  have hp : 0 ≤ S ^ (1 / 2 - α) := Real.rpow_nonneg (zero_le_one.trans hS) _
  nlinarith only [hα', hp]

/-- Multiplying an actual j-th coefficient tail by the signed force gives
precisely the common order s^(d+2alpha), uniformly over j<=d. -/
theorem kernel_remainder_coefficient_tail_bound (d j : ℕ) (hj : j ≤ d)
    (α C : ℝ) (hα : 0 < α) (hC : 0 < C)
    (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
    (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hb : ∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
      ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
        C * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2))
    (hi : IntegrableOn (fun t : ℝ => iteratedDeriv j (fun x : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
        (j.factorial : ℝ)) (Ici 0))
    {lam : ℝ} (hl : 0 < |lam|) (hs : |lam| ≤ 1) :
    (∫ t in Ici (1 / |lam| ^ 2), |iteratedDeriv j (fun x : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
        (j.factorial : ℝ)|) * |lam| ^ j ≤
      (C * Real.exp (4 * C) / α) * |lam| ^ ((d : ℝ) + 2 * α) := by
  let β : ℝ := ((d : ℝ) - j) / 2 + α
  have hdj : (j : ℝ) ≤ d := by exact_mod_cast hj
  have hβ : 0 < β := by dsimp only [β]; linarith
  have hαβ : α ≤ β := by dsimp only [β]; linarith
  have hS : 1 ≤ 1 / |lam| ^ 2 := by
    apply (le_div_iff₀ (pow_pos hl 2)).mpr
    simpa using pow_le_one₀ (n := 2) hl.le hs
  have hi' := hi.mono_set (Ici_subset_Ici.mpr ((zero_le_one.trans hS)))
  have hpow : IntegrableOn (fun t : ℝ =>
      (C * Real.exp (4 * C)) * t ^ (-1 - β)) (Ici (1 / |lam| ^ 2)) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity))).const_mul _
  have H := setIntegral_mono_on hi'.abs hpow measurableSet_Ici (fun t ht => by
    have hh := kernel_remainder_coefficient_large_bound d α C u₀ u₂ γ K hK hb j
      (hS.trans ht)
    simpa only [β, show -1 - ((d : ℝ) - j) / 2 - α =
      -1 - (((d : ℝ) - j) / 2 + α) by ring] using hh)
  rw [integral_const_mul, integral_force_cutoff_power hl hβ] at H
  apply (mul_le_mul_of_nonneg_right H (pow_nonneg hl.le j)).trans
  have he : |lam| ^ (2 * β) * |lam| ^ j = |lam| ^ ((d : ℝ) + 2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hl]
    congr 1
    dsimp only [β]
    ring
  calc
    _ = ((C * Real.exp (4 * C)) / β) *
        (|lam| ^ (2 * β) * |lam| ^ j) := by ring
    _ = ((C * Real.exp (4 * C)) / β) * |lam| ^ ((d : ℝ) + 2 * α) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity) hα hαβ) (by positivity)

/-- The integrated fixed-disc Taylor error, with the actual signed powers and
literal real iterated derivatives, has the source order s^(d+2alpha). -/
theorem kernel_remainder_taylor_integral_bound (d : ℕ) (α C : ℝ)
    (hα : 0 < α) (hα' : α ≤ 1 / 4) (hC : 0 < C)
    (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
    (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hb : ∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
      ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
        C * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2))
    {lam : ℝ} (hl : 0 < |lam|) (hs : |lam| ≤ 1)
    (hi : IntegrableOn (fun t : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re -
        ∑ j : Fin (d + 1), (iteratedDeriv j.val (fun x : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) * lam ^ j.val) (Icc 1 (1 / |lam| ^ 2))) :
    (∫ t in Icc (1 : ℝ) (1 / |lam| ^ 2),
      |(kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re -
        ∑ j : Fin (d + 1), (iteratedDeriv j.val (fun x : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) * lam ^ j.val|) ≤
      (4 * ((d + 1 : ℕ) : ℝ) * (C * Real.exp (9 * C))) *
        |lam| ^ ((d : ℝ) + 2 * α) := by
  have hS : 1 ≤ 1 / |lam| ^ 2 := by
    apply (le_div_iff₀ (pow_pos hl 2)).mpr
    simpa using pow_le_one₀ (n := 2) hl.le hs
  have hp : IntegrableOn (fun t : ℝ => t ^ (-1 / 2 - α))
      (Icc (1 : ℝ) (1 / |lam| ^ 2)) :=
    (continuousOn_id.rpow_const (fun t ht => Or.inl
      (ne_of_gt (zero_lt_one.trans_le ht.1)))).integrableOn_Icc
  have H := setIntegral_mono_on hi.abs
    (hp.const_mul (((d + 1 : ℕ) : ℝ) * (C * Real.exp (9 * C)) * |lam| ^ (d + 1)))
    measurableSet_Icc (fun t ht => by
      apply kernel_remainder_taylor_large_bound d α C hC u₀ u₂ γ K hK hb ht.1 hl
      apply (sq_le_sq₀ (by positivity) zero_le_one).mp
      rw [mul_pow, Real.sq_sqrt (zero_le_one.trans ht.1), one_pow]
      simpa only [mul_comm] using (le_div_iff₀ (pow_pos hl 2)).mp ht.2)
  rw [integral_const_mul] at H
  apply H.trans
  have ht := mul_le_mul_of_nonneg_left (integral_taylor_time_power hα hα' hS)
    (show 0 ≤ ((d + 1 : ℕ) : ℝ) * (C * Real.exp (9 * C)) * |lam| ^ (d + 1) by positivity)
  apply ht.trans_eq
  rw [force_cutoff_rpow hl]
  have he : |lam| ^ (d + 1) * |lam| ^ (-2 * (1 / 2 - α)) =
      |lam| ^ ((d : ℝ) + 2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hl]
    congr 1
    push_cast
    ring
  calc
    _ = (4 * ((d + 1 : ℕ) : ℝ) * (C * Real.exp (9 * C))) *
        (|lam| ^ (d + 1) * |lam| ^ (-2 * (1 / 2 - α))) := by ring
    _ = _ := by rw [he]

/-- The growing time interval lies in one actual real profile window. The
constant sqrt(B) is chosen before force and time. -/
theorem growing_logarithmic_window_inclusion {s B t : ℝ}
    (hs : 0 < s) (hsmall : s ≤ Real.exp (-1)) (hB : 0 < B)
    (ht : 1 / s ^ 2 ≤ t)
    (htB : t ≤ B / s ^ 2 * Real.sqrt (Real.log (1 / s))) :
    s * Real.sqrt t ≤ Real.sqrt B * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) := by
  have ht₀ : 0 < t := (div_pos zero_lt_one (pow_pos hs 2)).trans_le ht
  have hL : 1 ≤ Real.log (1 / s) := by
    simpa only [abs_of_pos hs] using one_le_log_inv_abs (lam := s)
      (by simpa only [abs_of_pos hs] using hs) (by simpa only [abs_of_pos hs] using hsmall)
  have hst : 1 / s ≤ Real.sqrt t := by
    apply (Real.le_sqrt (by positivity) ht₀.le).mpr
    simpa only [div_pow, one_pow] using ht
  have hlog : Real.log (1 / s) ≤ Real.log (Real.sqrt t) :=
    Real.log_le_log (by positivity) hst
  have hlog₀ : 0 ≤ Real.log (Real.sqrt t) := zero_le_one.trans (hL.trans hlog)
  have hsq : (s * Real.sqrt t) ^ 2 ≤ B * Real.sqrt (Real.log (1 / s)) := by
    rw [mul_pow, Real.sq_sqrt ht₀.le]
    calc
      _ ≤ s ^ 2 * (B / s ^ 2 * Real.sqrt (Real.log (1 / s))) :=
        mul_le_mul_of_nonneg_left htB (sq_nonneg s)
      _ = _ := by field_simp
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow]
  rw [Real.sq_sqrt hB.le, ← Real.rpow_mul_natCast hlog₀]
  rw [mul_pow] at hsq
  norm_num only [show (1 / 4 : ℝ) * (2 : ℕ) = 1 / 2 by norm_num]
  rw [← Real.sqrt_eq_rpow]
  exact hsq.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog) hB.le)

/-- On the growing interval the profile exponential is at most exp(A*sqrt L)
with A depending only on the already fixed window and cutoff constants. -/
theorem growing_logarithmic_window_exponential_bound {s B W t : ℝ}
    (hs : 0 < s) (hsmall : s ≤ Real.exp (-1)) (hW : 0 ≤ W)
    (ht₀ : 0 ≤ t) (ht : t ≤ B / s ^ 2 * Real.sqrt (Real.log (1 / s))) :
    Real.exp (W * (1 + s * Real.sqrt t) ^ 2) ≤
      Real.exp ((W * (2 + 2 * B)) * Real.sqrt (Real.log (1 / s))) := by
  have hL : 1 ≤ Real.log (1 / s) := by
    simpa only [abs_of_pos hs] using one_le_log_inv_abs (lam := s)
      (by simpa only [abs_of_pos hs] using hs) (by simpa only [abs_of_pos hs] using hsmall)
  have hL' : 1 ≤ Real.sqrt (Real.log (1 / s)) := by
    exact (Real.le_sqrt zero_le_one (zero_le_one.trans hL)).mpr (by simpa using hL)
  have hx : (s * Real.sqrt t) ^ 2 ≤ B * Real.sqrt (Real.log (1 / s)) := by
    rw [mul_pow, Real.sq_sqrt ht₀]
    calc
      _ ≤ s ^ 2 * (B / s ^ 2 * Real.sqrt (Real.log (1 / s))) :=
        mul_le_mul_of_nonneg_left ht (sq_nonneg s)
      _ = _ := by field_simp
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ W * ((2 + 2 * B) * Real.sqrt (Real.log (1 / s))) := by
      apply mul_le_mul_of_nonneg_left _ hW
      nlinarith only [sq_nonneg (1 - s * Real.sqrt t), hx, hL']
    _ = _ := by ring

/-- Integrate the actual real-window profile error over the growing interval.
Measurability and integrability are constructed from the standing pointwise
hypotheses; the majorant is integrated on the full force-cutoff half-line. -/
theorem kernel_remainder_growing_window_integral_bound (d : ℕ) (α : ℝ) (hα : 0 < α)
    (B : ℝ) (hB : 0 < B) (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
    (hm : ∀ z : ℂ, Measurable (fun t : ℝ => K t z))
    (Cw Tw : ℝ → ℝ) (hW : 0 < Cw (Real.sqrt B))
    (hw : ∀ C₀ : ℝ, 0 < C₀ → ∀ t : ℝ, Tw C₀ ≤ t →
      ∀ lam : ℝ, |lam| * Real.sqrt t ≤
          C₀ * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) →
      ‖kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)‖ ≤
        Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2))
    {lam : ℝ} (hl : 0 < |lam|) (hs : |lam| ≤ Real.exp (-1))
    (hstart : Tw (Real.sqrt B) ≤ 1 / |lam| ^ 2) :
    IntegrableOn (fun t : ℝ => kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ))
      (Icc (1 / |lam| ^ 2) (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|)))) ∧
    (∫ t in Icc (1 / |lam| ^ 2) (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))),
      ‖kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)‖) ≤
      (Cw (Real.sqrt B) / α) * |lam| ^ ((d : ℝ) + 2 * α) *
        Real.exp ((Cw (Real.sqrt B) * (2 + 2 * B)) *
          Real.sqrt (Real.log (1 / |lam|))) := by
  let β : ℝ := (d : ℝ) / 2 + α
  have hαβ : α ≤ β := by dsimp only [β]; linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hβ : 0 < β := hα.trans_le hαβ
  let M : ℝ := Cw (Real.sqrt B) *
    Real.exp ((Cw (Real.sqrt B) * (2 + 2 * B)) * Real.sqrt (Real.log (1 / |lam|)))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hp : IntegrableOn (fun t : ℝ => M * t ^ (-1 - β)) (Ici (1 / |lam| ^ 2)) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity))).const_mul _
  have hp' := hp.mono_set (Icc_subset_Ici_self :
    Icc (1 / |lam| ^ 2) (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))) ⊆
      Ici (1 / |lam| ^ 2))
  have hb : ∀ t ∈ Icc (1 / |lam| ^ 2)
      (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))),
      ‖kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)‖ ≤ M * t ^ (-1 - β) := by
    intro t ht
    have ht₀ : 0 ≤ t := (by positivity : 0 ≤ 1 / |lam| ^ 2).trans ht.1
    have hh := hw (Real.sqrt B) (Real.sqrt_pos.mpr hB) t (hstart.trans ht.1) lam
      (growing_logarithmic_window_inclusion hl hs hB ht.1 ht.2)
    have he := growing_logarithmic_window_exponential_bound hl hs hW.le ht₀ ht.2
    calc
      _ ≤ _ := hh
      _ ≤ Cw (Real.sqrt B) * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp ((Cw (Real.sqrt B) * (2 + 2 * B)) *
            Real.sqrt (Real.log (1 / |lam|))) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by
        dsimp only [M, β]
        rw [show -1 - (d : ℝ) / 2 - α = -1 - ((d : ℝ) / 2 + α) by ring]
        ring
  have hi := hp'.mono'
    (measurable_kernelProfileRemainder d u₀ u₂ γ K hm (lam : ℂ)).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hb t ht)
  refine ⟨hi, ?_⟩
  have H := setIntegral_mono_on hi.norm hp' measurableSet_Icc hb
  have H' := setIntegral_mono_set (s := Icc (1 / |lam| ^ 2)
      (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|)))) hp
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact mul_nonneg hM (Real.rpow_nonneg
        ((by positivity : 0 ≤ 1 / |lam| ^ 2).trans ht) _))
    (Filter.Eventually.of_forall (fun t ht => ht.1))
  apply (H.trans H').trans
  rw [integral_const_mul, integral_force_cutoff_power hl hβ]
  have he : 2 * β = (d : ℝ) + 2 * α := by dsimp only [β]; ring
  rw [he]
  calc
    _ = ((Cw (Real.sqrt B) / β) * |lam| ^ ((d : ℝ) + 2 * α)) *
        Real.exp ((Cw (Real.sqrt B) * (2 + 2 * B)) *
          Real.sqrt (Real.log (1 / |lam|))) := by dsimp only [M]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hW.le hα hαβ) (by positivity))
      (Real.exp_nonneg _)

end EinsteinFull
