import EinsteinFull.Work.W4.KernelErrorAssemblySupport

/-! Completion of the literal integrated-error argument below the frozen
kernel-integration anchor. -/

open MeasureTheory Set

namespace EinsteinFull

/-- The actual kernel tail at any sufficiently large common logarithmic cutoff.
This permits the same structural B to control both kernel and model tails. -/
theorem kernel_common_logarithmic_tail_bound (d : ℕ) (C c C_T B : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hB : 0 < B)
    (hBT : C_T ≤ B) (hdecay : C + 4 ≤ c * B)
    (K : ℝ → ℂ → ℂ) (hm : ∀ z : ℂ, Measurable (fun t : ℝ => K t z))
    (htail : ∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
      ∀ t : ℝ, C_T / |lam| ^ 2 ≤ t →
      ‖K t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
        Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t))
    {lam : ℝ} (hl : 0 < |lam|) (hs : |lam| ≤ Real.exp (-1)) :
    IntegrableOn (fun t : ℝ => K t (lam : ℂ))
      (Ici (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|)))) ∧
    (∫ t in Ici (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))),
      ‖K t (lam : ℂ)‖) ≤ (C / c) * |lam| ^ d *
        Real.exp (-4 * Real.sqrt (Real.log (1 / |lam|))) := by
  have hL : 1 ≤ Real.sqrt (Real.log (1 / |lam|)) :=
    (Real.le_sqrt zero_le_one (zero_le_one.trans (one_le_log_inv_abs hl hs))).mpr
      (by simpa using one_le_log_inv_abs hl hs)
  have hA : C_T / |lam| ^ 2 ≤ B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|)) :=
    (div_le_div_of_nonneg_right hBT (sq_nonneg _)).trans
      (le_mul_of_one_le_right (by positivity) hL)
  obtain ⟨hi, hb⟩ := kernel_tail_integral_bound d C c C_T hc K hm htail hl hs hA
  refine ⟨hi, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have he : C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 *
      (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))) =
      (C - c * B) * Real.sqrt (Real.log (1 / |lam|)) := by
    rw [sq_abs]
    field_simp [abs_pos.mp hl]
  rw [he]
  exact mul_le_mul_of_nonneg_right (by linarith only [hdecay]) (Real.sqrt_nonneg _)

/-- Integrating the four actual time regions gives the quantitative error
before the final structural small-force absorption. The coefficient and kernel
integrability data are the already constructed literal witnesses. -/
theorem kernel_remainder_integrated_error_bound (d : ℕ) (α C c C_T B : ℝ)
    (hα : 0 < α) (hα' : α ≤ 1 / 4) (hC : 0 < C) (hc : 0 < c)
    (hB : 1 ≤ B) (hBT : C_T ≤ B) (hdecK : C + 4 ≤ c * B)
    (hdecG : 4 ≤ c / 2 * B)
    (Cw Tw : ℝ → ℝ) (hW : 0 < Cw (Real.sqrt B))
    (u₀ u₂ γ : ℝ) (hγ : 0 < γ) (K : ℝ → ℂ → ℂ)
    (ha : |u₀| + |u₂| ≤ C) (hγc : c ≤ γ)
    (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hm : ∀ z : ℂ, Measurable (fun t : ℝ => K t z))
    (hR : ∀ t : ℝ, 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0)
    (hinit : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C)
    (hfixed : ∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
      ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
        C * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2))
    (hwindow : ∀ C₀ : ℝ, 0 < C₀ → ∀ t : ℝ, Tw C₀ ≤ t →
      ∀ lam : ℝ, |lam| * Real.sqrt t ≤
          C₀ * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) →
      ‖kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)‖ ≤
        Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2))
    (htail : ∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
      ∀ t : ℝ, C_T / |lam| ^ 2 ≤ t →
      ‖K t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
        Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t))
    (hI : ∀ j : Fin (d + 1), IntegrableOn (fun t : ℝ =>
      iteratedDeriv j.val (fun x : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
          (j.val.factorial : ℝ)) (Ici 0))
    {lam : ℝ} (hl : 0 < |lam|) (hs : |lam| ≤ Real.exp (-1))
    (hstart : Tw (Real.sqrt B) ≤ 1 / |lam| ^ 2)
    (hiK : IntegrableOn (fun t : ℝ => (K t (lam : ℂ)).re) (Ici 0)) :
    |(∫ t in Ici (0 : ℝ), (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) -
      ∑ j : Fin (d + 1), integratedRemainderCoefficient d u₀ u₂ γ K hK hR j (hI j) *
        lam ^ j.val| ≤
      (((d + 1 : ℕ) : ℝ) * C) * |lam| ^ (d + 1) +
      (4 * ((d + 1 : ℕ) : ℝ) * (C * Real.exp (9 * C)) +
        ((d + 1 : ℕ) : ℝ) * (C * Real.exp (4 * C) / α)) *
          |lam| ^ ((d : ℝ) + 2 * α) +
      (Cw (Real.sqrt B) / α) * |lam| ^ ((d : ℝ) + 2 * α) *
        Real.exp ((Cw (Real.sqrt B) * (2 + 2 * B)) *
          Real.sqrt (Real.log (1 / |lam|))) +
      (C / c + 2 * C * (1 + 2 / c) / c) * |lam| ^ d *
        Real.exp (-4 * Real.sqrt (Real.log (1 / |lam|))) := by
  let E : ℝ → ℝ := fun t => (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re
  let a : Fin (d + 1) → ℝ → ℝ := fun j t => iteratedDeriv j.val (fun x : ℝ =>
    (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 / (j.val.factorial : ℝ)
  let P : ℝ → ℝ := fun t => ∑ j : Fin (d + 1), a j t * lam ^ j.val
  let S : ℝ := 1 / |lam| ^ 2
  let T : ℝ := B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))
  let G : ℝ → ℝ := fun t => t ^ (-1 - (d : ℝ) / 2) *
    gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)
  have hs₁ : |lam| ≤ 1 := hs.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hS : 1 ≤ S := by
    apply (le_div_iff₀ (pow_pos hl 2)).mpr
    simpa using pow_le_one₀ (n := 2) hl.le hs₁
  have hL : 1 ≤ Real.sqrt (Real.log (1 / |lam|)) :=
    (Real.le_sqrt zero_le_one (zero_le_one.trans (one_le_log_inv_abs hl hs))).mpr
      (by simpa using one_le_log_inv_abs hl hs)
  have hST : S ≤ T := (div_le_div_of_nonneg_right hB (sq_nonneg _)).trans
    (le_mul_of_one_le_right (by positivity) hL)
  have hiE : IntegrableOn E (Ici 0) :=
    (kernel_remainder_real_integral_identity d u₀ u₂ γ hγ K (abs_pos.mp hl) hiK).1
  have hiP : IntegrableOn P (Ici 0) :=
    integrable_finset_sum _ (fun j _ => (hI j).mul_const (lam ^ j.val))
  have heP : (∫ t in Ici (0 : ℝ), P t) =
      ∑ j : Fin (d + 1), integratedRemainderCoefficient d u₀ u₂ γ K hK hR j (hI j) *
        lam ^ j.val := by
    rw [show P = fun t => ∑ j : Fin (d + 1), a j t * lam ^ j.val from rfl,
      integral_finset_sum _ (fun j _ => (hI j).mul_const (lam ^ j.val))]
    simp only [integral_mul_const, integratedRemainderCoefficient]
  have hiEP : IntegrableOn (fun t => E t - P t) (Ici 0) := hiE.sub hiP
  have h₀ : (∫ t in Ioo (0 : ℝ) 1, |E t - P t|) ≤
      (((d + 1 : ℕ) : ℝ) * C) * |lam| ^ (d + 1) := by
    have hi : IntegrableOn (fun t => E t - P t) (Ioo (0 : ℝ) 1) :=
      hiEP.mono_set (fun _ ht => ht.1.le)
    have H := setIntegral_mono_on hi.abs (integrableOn_const (C :=
      (((d + 1 : ℕ) : ℝ) * C) * |lam| ^ (d + 1)) (hs := measure_Ioo_lt_top.ne))
      measurableSet_Ioo (fun t ht =>
        kernel_remainder_taylor_initial_bound d u₀ u₂ γ C K hK hinit ht.1.le ht.2 hl hs₁)
    simpa only [setIntegral_const, measureReal_def, Real.volume_Ioo,
      sub_zero, ENNReal.toReal_ofReal zero_le_one, smul_eq_mul, one_mul] using H
  have h₁ : (∫ t in Ioo (1 : ℝ) S, |E t - P t|) ≤
      (4 * ((d + 1 : ℕ) : ℝ) * (C * Real.exp (9 * C))) *
        |lam| ^ ((d : ℝ) + 2 * α) := by
    rw [← integral_Icc_eq_integral_Ioo]
    exact kernel_remainder_taylor_integral_bound d α C hα hα' hC u₀ u₂ γ K hK hfixed
      hl hs₁ (hiEP.mono_set (fun _ ht => zero_le_one.trans ht.1))
  have h₂ : (∫ t in Ioo S T, |E t|) ≤
      (Cw (Real.sqrt B) / α) * |lam| ^ ((d : ℝ) + 2 * α) *
        Real.exp ((Cw (Real.sqrt B) * (2 + 2 * B)) *
          Real.sqrt (Real.log (1 / |lam|))) := by
    obtain ⟨hi, hb⟩ := kernel_remainder_growing_window_integral_bound d α hα B
      (zero_lt_one.trans_le hB) u₀ u₂ γ K hm Cw Tw hW hwindow hl hs hstart
    rw [← integral_Icc_eq_integral_Ioo]
    exact (setIntegral_mono_on
      ((hiE.mono_set (fun _ ht => (zero_le_one.trans hS).trans ht.1)).abs)
      hi.norm measurableSet_Icc (fun t _ => Complex.abs_re_le_norm _)).trans hb
  have htK := kernel_common_logarithmic_tail_bound d C c C_T B hC hc
    (zero_lt_one.trans_le hB) hBT hdecK K hm htail hl hs
  have htG := gaussian_time_profile_tail_integral_bound d u₀ u₂ γ C c ha hc hγc hl hST
  have h₃ : (∫ t in Ici T, |E t|) ≤
      (C / c + 2 * C * (1 + 2 / c) / c) * |lam| ^ d *
        Real.exp (-4 * Real.sqrt (Real.log (1 / |lam|))) := by
    have H := setIntegral_mono_on
      ((hiE.mono_set (Ici_subset_Ici.mpr ((zero_le_one.trans hS).trans hST))).abs)
      (htK.1.norm.add htG.1.abs) measurableSet_Ici (fun t ht => by
        have ht₁ : 1 ≤ t := (hS.trans hST).trans ht
        have he : E t = (K t (lam : ℂ)).re - G t := by
          dsimp only [E, G, kernelProfileRemainder]
          rw [if_pos ht₁, ← Complex.ofReal_mul, complexGaussianProfile_ofReal,
            ← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re]
        rw [he]
        exact (abs_sub _ _).trans (add_le_add (Complex.abs_re_le_norm _) le_rfl))
    simp only [Pi.add_apply] at H
    rw [integral_add htK.1.norm htG.1.abs] at H
    apply H.trans
    have hg := gaussian_time_profile_logarithmic_tail_bound d u₀ u₂ γ C c B ha hc hγc
      hB hdecG hl hs
    have H' := add_le_add htK.2 hg
    convert H' using 1
    ring
  have h₄ : (∫ t in Ici S, |P t|) ≤
      ((d + 1 : ℕ) : ℝ) * (C * Real.exp (4 * C) / α) *
        |lam| ^ ((d : ℝ) + 2 * α) := by
    have hiS (j : Fin (d + 1)) := (hI j).mono_set
      (Ici_subset_Ici.mpr (zero_le_one.trans hS))
    have H := setIntegral_mono_on
      ((hiP.mono_set (Ici_subset_Ici.mpr (zero_le_one.trans hS))).abs)
      (integrable_finset_sum _ (fun j _ => (hiS j).abs.mul_const (|lam| ^ j.val)))
      measurableSet_Ici (fun t _ => by
        change |∑ j : Fin (d + 1), a j t * lam ^ j.val| ≤ _
        simpa only [abs_mul, abs_pow] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => a j t * lam ^ j.val)))
    rw [integral_finset_sum _ (fun j _ => (hiS j).abs.mul_const (|lam| ^ j.val))] at H
    simp only [integral_mul_const] at H
    apply H.trans
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      kernel_remainder_coefficient_tail_bound d j.val (by omega) α C hα hC
        u₀ u₂ γ K hK hfixed (hI j) hl hs₁)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc] using hh
  rw [← heP]
  exact (integral_four_region_error_bound hS hST hiE hiP).trans (by
    linarith only [h₀, h₁, h₂, h₃, h₄])

private theorem force_cutoff_above_window {s Q : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (hQ : 1 ≤ Q) (hsmall : s ≤ 1 / (Q + 1)) : Q ≤ 1 / s ^ 2 := by
  have hm : s * (Q + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp hsmall
  have hsq : Q * s ^ 2 ≤ 1 := by
    have hQs : s * Q ≤ 1 := by nlinarith only [hm, hs]
    calc
      _ = (s * Q) * s := by ring
      _ ≤ 1 * 1 := mul_le_mul hQs hs₁ hs.le zero_le_one
      _ = 1 := one_mul _
  exact (le_div_iff₀ (pow_pos hs 2)).mpr hsq

private theorem integrated_error_absorption (d : ℕ) (α A a b w q : ℝ)
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) (hq : 0 ≤ q)
    {s : ℝ} (hs : 0 < s) (hsmall : s ≤ Real.exp (-1))
    (habsorb : s ^ (2 * α) * Real.exp (A * Real.sqrt (Real.log (1 / s))) ≤
      Real.exp (-Real.sqrt (Real.log (1 / s)))) :
    a * s ^ (d + 1) + b * s ^ ((d : ℝ) + 2 * α) +
      w * s ^ ((d : ℝ) + 2 * α) * Real.exp (A * Real.sqrt (Real.log (1 / s))) +
      q * s ^ d * Real.exp (-4 * Real.sqrt (Real.log (1 / s))) ≤
      (a + b + w + q) * s ^ d * expansionModulus s hs hsmall := by
  have hpow : s ^ ((d : ℝ) + 2 * α) = s ^ d * s ^ (2 * α) := by
    rw [Real.rpow_add hs, Real.rpow_natCast]
  have hexp : 1 ≤ Real.exp (A * Real.sqrt (Real.log (1 / s))) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hA (Real.sqrt_nonneg _))
  have hbase : s ^ (2 * α) ≤ expansionModulus s hs hsmall :=
    (le_mul_of_one_le_right (by positivity) hexp).trans habsorb
  have htail : Real.exp (-4 * Real.sqrt (Real.log (1 / s))) ≤
      expansionModulus s hs hsmall := by
    apply Real.exp_le_exp.mpr
    nlinarith only [Real.sqrt_nonneg (Real.log (1 / s))]
  have h₀ := mul_le_mul_of_nonneg_left
    (force_pow_succ_le_expansionModulus d s hs hsmall) ha
  have h₁ := mul_le_mul_of_nonneg_left hbase (mul_nonneg hb (pow_nonneg hs.le d))
  have habsorb' : s ^ (2 * α) * Real.exp (A * Real.sqrt (Real.log (1 / s))) ≤
      expansionModulus s hs hsmall := habsorb
  have h₂ := mul_le_mul_of_nonneg_left habsorb' (mul_nonneg hw (pow_nonneg hs.le d))
  have h₃ := mul_le_mul_of_nonneg_left htail (mul_nonneg hq (pow_nonneg hs.le d))
  rw [hpow]
  nlinarith only [h₀, h₁, h₂, h₃]

/-- The full frozen kernel-integration contract, proved from its exact standing
hypotheses, including the final integrated-error conjunction. -/
theorem kernel_integration_complete (d : ℕ) (hd : 2 ≤ d)
    (α C c C_T : ℝ) (hα : 0 < α) (hα' : α ≤ 1 / 4)
    (hC : 0 < C) (hc : 0 < c) (hCT : 0 < C_T)
    (Cw Tw : ℝ → ℝ) (hCw : ∀ C₀, 0 < C₀ → 0 < Cw C₀)
    (hTw : ∀ C₀, 0 < C₀ → 1 ≤ Tw C₀) :
    ∃ C_out lam_star : ℝ, 0 < C_out ∧ 0 < lam_star ∧ lam_star ≤ Real.exp (-1) ∧
    ∀ (u₀ u₂ γ : ℝ) (hγ : 0 < γ) (K : ℝ → ℂ → ℂ),
      |u₀| + |u₂| ≤ C → c ≤ γ → γ ≤ C →
      ∀ hK : ∀ t : ℝ, 0 ≤ t → Differentiable ℂ (K t),
      (∀ z : ℂ, Measurable (fun t : ℝ => K t z)) →
      ∀ hR : ∀ (t : ℝ), 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0,
      (∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C) →
      (∀ (t : ℝ), 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)) →
      (∀ C₀ : ℝ, 0 < C₀ → ∀ (t : ℝ), Tw C₀ ≤ t →
        ∀ lam : ℝ, |lam| * Real.sqrt t ≤
            C₀ * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) →
        ‖kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)‖ ≤
          Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2)) →
      (∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
        ∀ t : ℝ, C_T / |lam| ^ 2 ≤ t →
        ‖K t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
          Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t)) →
      ∃ hI : ∀ j : Fin (d + 1),
        IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) (Set.Ici 0),
      (∀ j : Fin (d + 1),
        |integratedKernelCoefficient d u₀ u₂ γ hγ K hK hR hI j| ≤ C_out) ∧
      |integratedKernelCriticalCoefficient d u₀ u₂ γ hγ| ≤ C_out ∧
      ∀ lam : ℝ, ∀ h₀ : 0 < |lam|, ∀ h₁ : |lam| ≤ lam_star, ∀ hsmall : |lam| ≤ Real.exp (-1),
        IntegrableOn (fun t : ℝ => (K t (lam : ℂ)).re) (Set.Ici 0) ∧
        |(∫ t in Set.Ici (0 : ℝ), (K t (lam : ℂ)).re) -
          (∑ j : Fin (d + 1), integratedKernelCoefficient d u₀ u₂ γ hγ K hK hR hI j * lam ^ j.val) -
          integratedKernelCriticalCoefficient d u₀ u₂ γ hγ *
            criticalKernelTerm d lam (by intro h; simp [h] at h₀)| ≤
          C_out * |lam| ^ d * expansionModulus |lam| h₀ hsmall := by
  obtain ⟨R, s₀, hR, hs₀, hs₀small, hpref⟩ :=
    exists_uniform_kernel_coefficients_and_integrability d hd α C c C_T hα hC hc Cw Tw hCw hTw
  obtain ⟨M, hM, hmodel⟩ := exists_uniform_gaussianProfile_integrated_coefficient_bound d C c
  let B : ℝ := max 1 (max C_T (max ((C + 4) / c) (8 / c)))
  have hB : 1 ≤ B := le_max_left _ _
  have hBT : C_T ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hB₀ : 0 < B := hCT.trans_le hBT
  have hdecK : C + 4 ≤ c * B := by
    have hb : (C + 4) / c ≤ B :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hb
  have hdecG : 4 ≤ c / 2 * B := by
    have hb : 8 / c ≤ B :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hh := (div_le_iff₀ hc).mp hb
    linarith only [hh]
  let A : ℝ := Cw (Real.sqrt B) * (2 + 2 * B)
  have hW : 0 < Cw (Real.sqrt B) := hCw _ (Real.sqrt_pos.mpr hB₀)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨s₁, hs₁, _hs₁small, habsorb⟩ :=
    exists_force_threshold_rpow_exp_sqrt_log_bound α A 1 hα hA zero_le_one
  let a : ℝ := ((d + 1 : ℕ) : ℝ) * C
  let b : ℝ := 4 * ((d + 1 : ℕ) : ℝ) * (C * Real.exp (9 * C)) +
    ((d + 1 : ℕ) : ℝ) * (C * Real.exp (4 * C) / α)
  let w : ℝ := Cw (Real.sqrt B) / α
  let q : ℝ := C / c + 2 * C * (1 + 2 / c) / c
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let C_out : ℝ := R + (a + b + w + q) + M + 1
  let lam_star : ℝ := min s₀ (min s₁ (1 / (Tw (Real.sqrt B) + 1)))
  have hTwB : 1 ≤ Tw (Real.sqrt B) := hTw _ (Real.sqrt_pos.mpr hB₀)
  refine ⟨C_out, lam_star, by dsimp only [C_out]; positivity,
    lt_min hs₀ (lt_min hs₁ (by positivity)),
    (min_le_left _ _).trans hs₀small, ?_⟩
  intro u₀ u₂ γ hγ K hamp hγc hγC hK hm hreal hinit hfixed hwindow htail
  obtain ⟨hI, hcoeff, hcrit, hi⟩ := hpref u₀ u₂ γ hγ K hamp hγc hγC hK hm hreal
    hinit hfixed hwindow htail
  refine ⟨hI, fun j => (hcoeff j).trans ?_, hcrit.trans ?_, ?_⟩
  · dsimp only [C_out]
    linarith only [ha, hb, hw, hq, hM]
  · dsimp only [C_out]
    linarith only [ha, hb, hw, hq, hM]
  intro lam hl hls hsmall
  have hls₀ : |lam| ≤ s₀ := hls.trans (min_le_left _ _)
  have hls₁ : |lam| ≤ s₁ := hls.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlTw : |lam| ≤ 1 / (Tw (Real.sqrt B) + 1) :=
    hls.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsone : |lam| ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hiK := hi lam hl hls₀
  refine ⟨hiK, ?_⟩
  have hstart := force_cutoff_above_window hl hsone hTwB hlTw
  have herr := kernel_remainder_integrated_error_bound d α C c C_T B hα hα' hC hc hB
    hBT hdecK hdecG Cw Tw hW u₀ u₂ γ hγ K hamp hγc hK hm hreal hinit hfixed
    hwindow htail hI hl hsmall hstart hiK
  have habs := integrated_error_absorption d α A a b w q hA ha hb hw hq hl hsmall
    (by simpa only [neg_one_mul] using habsorb |lam| hl hls₁)
  have herr' : |(∫ t in Ici (0 : ℝ),
      (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) -
      ∑ j : Fin (d + 1), integratedRemainderCoefficient d u₀ u₂ γ K hK hreal j (hI j) *
        lam ^ j.val| ≤ (a + b + w + q) * |lam| ^ d * expansionModulus |lam| hl hsmall :=
    herr.trans habs
  have hmerr := hmodel u₀ u₂ γ hamp hγ hγc hγC K hK hreal hI lam (abs_pos.mp hl) hsone
  have hmid := (kernel_remainder_real_integral_identity d u₀ u₂ γ hγ K
    (abs_pos.mp hl) hiK).2
  let r : ℝ := ∑ j : Fin (d + 1),
    integratedRemainderCoefficient d u₀ u₂ γ K hK hreal j (hI j) * lam ^ j.val
  let p : ℝ := ∑ j : Fin (d + 1),
    integratedKernelCoefficient d u₀ u₂ γ hγ K hK hreal hI j * lam ^ j.val
  let z : ℝ := integratedKernelCriticalCoefficient d u₀ u₂ γ hγ *
    criticalKernelTerm d lam (abs_pos.mp hl)
  let g : ℝ := ∫ t in Ioi (1 : ℝ), t ^ (-1 - (d : ℝ) / 2) *
    gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)
  have he : (∫ t in Ici (0 : ℝ), (K t (lam : ℂ)).re) - p - z =
      ((∫ t in Ici (0 : ℝ),
        (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) - r) +
      ((r + g) - (p + z)) := by rw [hmid]; ring
  change |(∫ t in Ici (0 : ℝ), (K t (lam : ℂ)).re) - p - z| ≤ _
  rw [he]
  have H := (abs_add_le _ _).trans (add_le_add herr' hmerr)
  have hmPow := mul_le_mul_of_nonneg_left
    (force_pow_succ_le_expansionModulus d |lam| hl hsmall) hM
  apply H.trans
  have hmod : 0 ≤ |lam| ^ d * expansionModulus |lam| hl hsmall := by
    exact mul_nonneg (pow_nonneg hl.le d) (Real.exp_nonneg _)
  dsimp only [C_out]
  nlinarith only [hmPow, mul_nonneg hR.le hmod, hmod]

end EinsteinFull
