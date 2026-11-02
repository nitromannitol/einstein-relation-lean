import EinsteinFull.Work.W4.KernelCauchyCoefficientSupport

/-! Absolute tail integration of the actual kernel, and the structural choice
of its logarithmic cutoff before selecting any growing real window. -/

open MeasureTheory Set

namespace EinsteinFull

/-- Direct integration of the standing real-force tail bound. The conclusion
includes absolute complex integrability and retains both force signs. -/
theorem kernel_tail_integral_bound (d : ℕ) (C c C_T : ℝ)
    (hc : 0 < c) (K : ℝ → ℂ → ℂ)
    (hmeas : ∀ z : ℂ, Measurable (fun t : ℝ => K t z))
    (htail : ∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
      ∀ t : ℝ, C_T / |lam| ^ 2 ≤ t →
      ‖K t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
        Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t))
    {lam A : ℝ} (hlam : 0 < |lam|) (hsmall : |lam| ≤ Real.exp (-1))
    (hA : C_T / |lam| ^ 2 ≤ A) :
    IntegrableOn (fun t : ℝ => K t (lam : ℂ)) (Ici A) ∧
    (∫ t in Ici A, ‖K t (lam : ℂ)‖) ≤
      (C / c) * |lam| ^ d *
        Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * A) := by
  have hl : lam ≠ 0 := abs_pos.mp hlam
  have ha : -c * lam ^ 2 < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hc)
    (sq_pos_of_ne_zero hl)
  let D : ℝ := C * |lam| ^ (d + 2) *
    Real.exp (C * Real.sqrt (Real.log (1 / |lam|)))
  let g : ℝ → ℝ := fun t => D * Real.exp ((-c * lam ^ 2) * t)
  have hi : IntegrableOn g (Ici A) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      ((integrableOn_exp_mul_Ioi ha A).const_mul D)
  have hb : ∀ᵐ t ∂volume.restrict (Ici A), ‖K t (lam : ℂ)‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have h := htail lam hlam hsmall t (hA.trans ht)
    simpa only [g, D, sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc] using h
  have hK := hi.mono' (hmeas (lam : ℂ)).aestronglyMeasurable hb
  refine ⟨hK, (integral_mono_ae hK.norm hi hb).trans_eq ?_⟩
  change (∫ t in Ici A, D * Real.exp ((-c * lam ^ 2) * t)) = _
  rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_exp_mul_Ioi ha]
  dsimp only [D]
  rw [Real.exp_sub, show -c * lam ^ 2 * A = -(c * lam ^ 2 * A) by ring, Real.exp_neg]
  rw [pow_add, show |lam| ^ 2 = lam ^ 2 by exact sq_abs lam]
  field_simp [hc.ne', hl]

/-- The source small-force range makes its logarithmic scale at least one. -/
theorem one_le_log_inv_abs {lam : ℝ} (hlam : 0 < |lam|)
    (hsmall : |lam| ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / |lam|) := by
  have h := Real.log_le_log hlam hsmall
  rw [Real.log_exp] at h
  rw [one_div, Real.log_inv]
  linarith

/-- B is fixed only from the structural tail constants. Every later window
may be selected after B, while the actual integrated tail is already at most
`(C/c)*s^d*exp(-4*sqrt(log(1/s)))`. -/
theorem exists_uniform_kernel_logarithmic_tail_bound (d : ℕ) (C c C_T : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hCT : 0 < C_T) :
    ∃ B : ℝ, 0 < B ∧ C_T ≤ B ∧
      ∀ K : ℝ → ℂ → ℂ,
      (∀ z : ℂ, Measurable (fun t : ℝ => K t z)) →
      (∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
        ∀ t : ℝ, C_T / |lam| ^ 2 ≤ t →
        ‖K t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
          Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t)) →
      ∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
      IntegrableOn (fun t : ℝ => K t (lam : ℂ))
        (Ici (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|)))) ∧
      (∫ t in Ici (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))),
        ‖K t (lam : ℂ)‖) ≤
        (C / c) * |lam| ^ d * Real.exp (-4 * Real.sqrt (Real.log (1 / |lam|))) := by
  let B : ℝ := C_T + (C + 4) / c
  have hB : 0 < B := by dsimp [B]; positivity
  have hBT : C_T ≤ B := by
    exact le_add_of_nonneg_right (by positivity)
  have hdecay : C + 4 ≤ c * B := by
    dsimp only [B]
    have he : c * ((C + 4) / c) = C + 4 := mul_div_cancel₀ _ hc.ne'
    nlinarith [mul_pos hc hCT]
  refine ⟨B, hB, hBT, fun K hm ht lam hl hs => ?_⟩
  have hsq : 0 < |lam| ^ 2 := pow_pos hl _
  have hL : 1 ≤ Real.sqrt (Real.log (1 / |lam|)) := by
    exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      ((one_le_log_inv_abs hl hs).trans' zero_le_one)).2
      (by simpa using one_le_log_inv_abs hl hs)
  have hA : C_T / |lam| ^ 2 ≤ B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|)) :=
    (div_le_div_of_nonneg_right hBT hsq.le).trans
      (le_mul_of_one_le_right (by positivity) hL)
  obtain ⟨hi, hb⟩ := kernel_tail_integral_bound d C c C_T hc K hm ht hl hs hA
  refine ⟨hi, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have he : C * Real.sqrt (Real.log (1 / |lam|)) -
      c * lam ^ 2 * (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))) =
      (C - c * B) * Real.sqrt (Real.log (1 / |lam|)) := by
    rw [sq_abs]
    field_simp [(abs_pos.mp hl)]
  rw [he]
  exact mul_le_mul_of_nonneg_right (by linarith : C - c * B ≤ -4)
    (Real.sqrt_nonneg _)

end EinsteinFull
