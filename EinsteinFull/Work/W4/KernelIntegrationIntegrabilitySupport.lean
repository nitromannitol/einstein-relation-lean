import EinsteinFull.Work.W4.KernelIntegrationTailSupport
import EinsteinFull.Work.W4.GaussianTimeIntegralSupport
import EinsteinFull.Calculus.GaussianProfileSupport

/-! Absolute time integrability of the actual kernel from the standing
finite-time, fixed-disc, growing-window and real-tail hypotheses. -/

open MeasureTheory Set

namespace EinsteinFull

private theorem scaled_sqrt_le {s t Q : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (hQ : 0 ≤ Q) (h : t ≤ Q / s ^ 2) : s * Real.sqrt t ≤ Real.sqrt Q := by
  have hh : (s * Real.sqrt t) ^ 2 ≤ (Real.sqrt Q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hQ]
    simpa only [mul_comm] using (le_div_iff₀ (pow_pos hs 2)).mp h
  exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg Q)).mp hh

private theorem logarithmic_window_lower {s t : ℝ} (hs : 0 < s)
    (hsmall : s ≤ Real.exp (-1)) (ht : 1 / s ^ 2 ≤ t) :
    1 ≤ Real.log (Real.sqrt t) := by
  have ht₀ : 0 < t := (div_pos zero_lt_one (pow_pos hs 2)).trans_le ht
  have hsqrt : 1 / s ≤ Real.sqrt t := by
    apply (Real.le_sqrt (by positivity) ht₀.le).mpr
    simpa only [div_pow, one_pow] using ht
  have hlog : 1 ≤ Real.log (1 / s) := by
    have h := Real.log_le_log hs hsmall
    rw [Real.log_exp] at h
    rw [one_div, Real.log_inv]
    linarith
  exact hlog.trans (Real.log_le_log (by positivity) hsqrt)

/-- A structural force threshold gives absolute integrability of the actual
complex kernel, hence also its real part. Only standing source hypotheses are
used; no derivative, time-integrability or expansion premise is supplied.
The window families are fixed before the threshold and all kernel parameters. -/
theorem exists_uniform_kernel_integrability_threshold (d : ℕ)
    (α C c C_T : ℝ) (hα : 0 < α) (hC : 0 < C) (hc : 0 < c)
    (Cw Tw : ℝ → ℝ) (hCw : ∀ C₀, 0 < C₀ → 0 < Cw C₀)
    (hTw : ∀ C₀, 0 < C₀ → 1 ≤ Tw C₀) :
    ∃ lam_star : ℝ, 0 < lam_star ∧ lam_star ≤ Real.exp (-1) ∧
    ∀ (u₀ u₂ γ : ℝ) (hγ : 0 < γ) (K : ℝ → ℂ → ℂ),
      (∀ z : ℂ, Measurable (fun t : ℝ => K t z)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C) →
      (∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)) →
      (∀ C₀ : ℝ, 0 < C₀ → ∀ t : ℝ, Tw C₀ ≤ t →
        ∀ lam : ℝ, |lam| * Real.sqrt t ≤
            C₀ * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) →
        ‖kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)‖ ≤
          Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2)) →
      (∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
        ∀ t : ℝ, C_T / |lam| ^ 2 ≤ t →
        ‖K t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
          Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t)) →
      ∀ lam : ℝ, 0 < |lam| → |lam| ≤ lam_star →
      IntegrableOn (fun t : ℝ => K t (lam : ℂ)) (Ici 0) ∧
      IntegrableOn (fun t : ℝ => (K t (lam : ℂ)).re) (Ici 0) := by
  let Q : ℝ := max C_T 1
  let C₀ : ℝ := Real.sqrt Q
  have hQ : 1 ≤ Q := le_max_right _ _
  have hC₀ : 0 < C₀ := Real.sqrt_pos.mpr (zero_lt_one.trans_le hQ)
  have hTw₀ : 1 ≤ Tw C₀ := hTw C₀ hC₀
  let lam_star : ℝ := min (Real.exp (-1)) (1 / (Tw C₀ + 1))
  have hstar : 0 < lam_star := lt_min (Real.exp_pos _) (by positivity)
  refine ⟨lam_star, hstar, min_le_left _ _, ?_⟩
  intro u₀ u₂ γ hγ K hm hinit hfixed hwindow htail lam hl hls
  have hs : |lam| ≤ Real.exp (-1) := hls.trans (min_le_left _ _)
  have hs₁ : |lam| ≤ 1 := hs.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hsTw : |lam| * (Tw C₀ + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < Tw C₀ + 1)).mp (hls.trans (min_le_right _ _))
  have hstart : Tw C₀ ≤ 1 / |lam| ^ 2 := by
    apply (le_div_iff₀ (pow_pos hl 2)).mpr
    have hst : |lam| * Tw C₀ ≤ 1 := by nlinarith only [hsTw, hl]
    calc
      Tw C₀ * |lam| ^ 2 = (|lam| * Tw C₀) * |lam| := by ring
      _ ≤ 1 * 1 := mul_le_mul hst hs₁ hl.le zero_le_one
      _ = 1 := one_mul 1
  let T : ℝ := Q / |lam| ^ 2
  have hpower (t : ℝ) (ht : 1 ≤ t) : t ^ (-1 - (d : ℝ) / 2 - α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (by
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith)
  have hbound : ∀ t ∈ Icc (0 : ℝ) T,
      ‖kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)‖ ≤
        C + C * Real.exp (4 * C) + Cw C₀ * Real.exp (Cw C₀ * (1 + C₀) ^ 2) := by
    intro t ht
    by_cases ht₁ : t < 1
    · have he : kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ) = K t (lam : ℂ) := by
        simp only [kernelProfileRemainder, if_neg (not_le_of_gt ht₁), sub_zero]
      rw [he]
      have hb := hinit t ht.1 ht₁.le (lam : ℂ) (by simpa using hs₁.trans (by norm_num : (1 : ℝ) ≤ 2))
      have hn := (hCw C₀ hC₀).le
      linarith [mul_nonneg hC.le (Real.exp_nonneg (4 * C)),
        mul_nonneg hn (Real.exp_nonneg (Cw C₀ * (1 + C₀) ^ 2))]
    · have ht₁ : 1 ≤ t := le_of_not_gt ht₁
      by_cases htf : t ≤ 1 / |lam| ^ 2
      · have hscaled : |lam| * Real.sqrt t ≤ 1 := by
          simpa only [Real.sqrt_one] using scaled_sqrt_le hl ht.1 zero_le_one htf
        have hb := hfixed t ht₁ (lam : ℂ) (by simpa using hscaled.trans (by norm_num : (1 : ℝ) ≤ 2))
        have he : Real.exp (C * (1 + |lam| * Real.sqrt t) ^ 2) ≤ Real.exp (4 * C) := by
          apply Real.exp_le_exp.mpr
          have hn : 0 ≤ |lam| * Real.sqrt t := by positivity
          have hv : (1 + |lam| * Real.sqrt t) ^ 2 ≤ 4 := by nlinarith only [hn, hscaled]
          exact (mul_le_mul_of_nonneg_left hv hC.le).trans_eq (mul_comm _ _)
        rw [Complex.norm_real, Real.norm_eq_abs] at hb
        have hp := mul_le_mul (hpower t ht₁) he (Real.exp_nonneg _) zero_le_one
        have hbb : C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + |lam| * Real.sqrt t) ^ 2) ≤ C * Real.exp (4 * C) := by
          simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_left hp hC.le
        have hn := (hCw C₀ hC₀).le
        linarith [mul_nonneg hn (Real.exp_nonneg (Cw C₀ * (1 + C₀) ^ 2))]
      · have htf : 1 / |lam| ^ 2 ≤ t := (lt_of_not_ge htf).le
        have hscaled : |lam| * Real.sqrt t ≤ C₀ :=
          scaled_sqrt_le hl ht.1 (zero_le_one.trans hQ) ht.2
        have hlog : 1 ≤ Real.log (Real.sqrt t) := logarithmic_window_lower hl hs htf
        have hw : |lam| * Real.sqrt t ≤ C₀ * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) :=
          hscaled.trans (le_mul_of_one_le_right hC₀.le
            (Real.one_le_rpow hlog (by norm_num)))
        have hb := hwindow C₀ hC₀ t (hstart.trans htf) lam hw
        have he : Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2) ≤
            Real.exp (Cw C₀ * (1 + C₀) ^ 2) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ (hCw C₀ hC₀).le
          exact pow_le_pow_left₀ (by positivity) (by linarith) 2
        have hp := mul_le_mul (hpower t ht₁) he (Real.exp_nonneg _) zero_le_one
        have hbb : Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2) ≤
            Cw C₀ * Real.exp (Cw C₀ * (1 + C₀) ^ 2) := by
          simpa only [mul_assoc, one_mul] using
            mul_le_mul_of_nonneg_left hp (hCw C₀ hC₀).le
        have hn : 0 ≤ C * Real.exp (4 * C) := by positivity
        linarith
  have hiE : IntegrableOn (fun t : ℝ =>
      kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)) (Icc 0 T) := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_kernelProfileRemainder d u₀ u₂ γ K hm (lam : ℂ)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbound t ht
  have hiG : IntegrableOn (fun t : ℝ =>
      if 1 ≤ t then ((t ^ (-1 - (d : ℝ) / 2) *
        gaussianProfile u₀ u₂ γ (lam * Real.sqrt t) : ℝ) : ℂ) else 0) (Icc 0 T) := by
    have hi := Complex.ofRealCLM.integrable_comp
      ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
        (gaussianProfile_time_integral d u₀ u₂ hγ (abs_pos.mp hl)).1)
    exact (IntegrableOn.integrable_indicator hi measurableSet_Ici).integrableOn
  have hiK : IntegrableOn (fun t : ℝ => K t (lam : ℂ)) (Icc 0 T) := by
    apply IntegrableOn.congr_fun (hiE.add hiG) _ measurableSet_Icc
    intro t _
    change kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ) +
      (if 1 ≤ t then ((t ^ (-1 - (d : ℝ) / 2) *
        gaussianProfile u₀ u₂ γ (lam * Real.sqrt t) : ℝ) : ℂ) else 0) = K t (lam : ℂ)
    unfold kernelProfileRemainder
    split_ifs
    · rw [← Complex.ofReal_mul, complexGaussianProfile_ofReal, ← Complex.ofReal_mul]
      exact sub_add_cancel _ _
    · exact sub_add_cancel _ _
  have hiTail := (kernel_tail_integral_bound d C c C_T hc K hm htail (A := T) hl hs
    (div_le_div_of_nonneg_right (le_max_left C_T 1) (sq_nonneg _))).1
  have hi : IntegrableOn (fun t : ℝ => K t (lam : ℂ)) (Ici 0) :=
    (hiK.union hiTail).mono_set (by
      intro t ht
      by_cases htT : t ≤ T
      · exact Or.inl ⟨ht, htT⟩
      · exact Or.inr (le_of_lt (lt_of_not_ge htT)))
  exact ⟨hi, Complex.reCLM.integrable_comp hi⟩

end EinsteinFull
