import EinsteinFull.Work.W4.KernelIntegratedErrorSupport

/-! Quantitative Gaussian model tail on the same logarithmic cutoff as the
actual kernel. All rates are the literal rates of the source profile. -/

open MeasureTheory Set

namespace EinsteinFull

private theorem gaussian_polynomial_absorption {c γ x : ℝ}
    (hc : 0 < c) (hγ : c ≤ γ) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-γ * x) ≤ (1 + 2 / c) * Real.exp (-(c / 2) * x) := by
  have he : Real.exp (-(c / 2) * x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [hc, hx])
  have hxe : x * Real.exp (-(c / 2) * x) ≤ 2 / c := by
    have hh : (c / 2 * x) ≤ Real.exp (c / 2 * x) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg (-(c / 2) * x))
    have hid : Real.exp (c / 2 * x) * Real.exp (-(c / 2) * x) = 1 := by
      rw [← Real.exp_add, show c / 2 * x + -(c / 2) * x = 0 by ring, Real.exp_zero]
    rw [hid] at hh'
    apply (le_div_iff₀ hc).mpr
    nlinarith only [hh']
  calc
    _ ≤ (1 + x) * Real.exp (-c * x) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (by nlinarith only [hγ, hx])) (by positivity)
    _ = ((1 + x) * Real.exp (-(c / 2) * x)) * Real.exp (-(c / 2) * x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith only [he, hxe]) (Real.exp_nonneg _)

/-- A literal Gaussian profile bound retaining its amplitude and lower-rate
constants, before any time integration. -/
theorem gaussianProfile_uniform_exponential_bound (u₀ u₂ γ C c x : ℝ)
    (ha : |u₀| + |u₂| ≤ C) (hc : 0 < c) (hγ : c ≤ γ) :
    |gaussianProfile u₀ u₂ γ x| ≤
      (C * (1 + 2 / c)) * Real.exp (-(c / 2) * x ^ 2) := by
  have hC : 0 ≤ C := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans ha
  have hb : |u₀ + u₂ * x ^ 2| ≤ C * (1 + x ^ 2) := by
    calc
      _ ≤ |u₀| + |u₂ * x ^ 2| := abs_add_le _ _
      _ = |u₀| + |u₂| * x ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
      _ ≤ (|u₀| + |u₂|) * (1 + x ^ 2) := by
        nlinarith only [abs_nonneg u₂, mul_nonneg (abs_nonneg u₀) (sq_nonneg x)]
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (by positivity)
  unfold gaussianProfile
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (C * (1 + x ^ 2)) * Real.exp (-γ * x ^ 2) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = C * ((1 + x ^ 2) * Real.exp (-γ * x ^ 2)) := by ring
    _ ≤ C * ((1 + 2 / c) * Real.exp (-(c / 2) * x ^ 2)) :=
      mul_le_mul_of_nonneg_left (gaussian_polynomial_absorption hc hγ (sq_nonneg x)) hC
    _ = _ := by ring

/-- Beyond the force cutoff, the Gaussian time integrand has an elementary
exponential majorant of size s^(d+2). -/
theorem gaussian_time_profile_tail_pointwise_bound (d : ℕ) (u₀ u₂ γ C c : ℝ)
    (ha : |u₀| + |u₂| ≤ C) (hc : 0 < c) (hγ : c ≤ γ)
    {lam t : ℝ} (hl : 0 < |lam|) (ht : 1 / |lam| ^ 2 ≤ t) :
    |t ^ (-1 - (d : ℝ) / 2) * gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)| ≤
      (C * (1 + 2 / c)) * |lam| ^ (d + 2) * Real.exp (-(c / 2) * lam ^ 2 * t) := by
  have ht₀ : 0 < t := (div_pos zero_lt_one (pow_pos hl 2)).trans_le ht
  have hp : t ^ (-1 - (d : ℝ) / 2) ≤ |lam| ^ (d + 2) := by
    apply (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 / |lam| ^ 2) ht
      (by have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith)).trans_eq
    rw [force_cutoff_rpow hl]
    have he : -2 * (-1 - (d : ℝ) / 2) = ((d + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht₀.le _)]
  have hmodel := gaussianProfile_uniform_exponential_bound u₀ u₂ γ C c
    (lam * Real.sqrt t) ha hc hγ
  rw [mul_pow, Real.sq_sqrt ht₀.le] at hmodel
  have hC : 0 ≤ C := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans ha
  calc
    _ ≤ |lam| ^ (d + 2) * ((C * (1 + 2 / c)) *
        Real.exp (-(c / 2) * (lam ^ 2 * t))) :=
      mul_le_mul hp hmodel (abs_nonneg _) (by positivity)
    _ = _ := by rw [mul_assoc (-(c / 2))]; ring

/-- Exact elementary integration of the Gaussian tail. No Mellin or finite-part
identity is needed for this absolute estimate. -/
theorem gaussian_time_profile_tail_integral_bound (d : ℕ) (u₀ u₂ γ C c : ℝ)
    (ha : |u₀| + |u₂| ≤ C) (hc : 0 < c) (hγ : c ≤ γ)
    {lam A : ℝ} (hl : 0 < |lam|) (hA : 1 / |lam| ^ 2 ≤ A) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - (d : ℝ) / 2) *
      gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)) (Ici A) ∧
    (∫ t in Ici A, |t ^ (-1 - (d : ℝ) / 2) *
      gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)|) ≤
      (2 * C * (1 + 2 / c) / c) * |lam| ^ d *
        Real.exp (-(c / 2) * lam ^ 2 * A) := by
  have hl₀ : lam ≠ 0 := abs_pos.mp hl
  have hr : -(c / 2) * lam ^ 2 < 0 := by
    exact mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero hl₀)
  let D : ℝ := (C * (1 + 2 / c)) * |lam| ^ (d + 2)
  let g : ℝ → ℝ := fun t => D * Real.exp ((-(c / 2) * lam ^ 2) * t)
  have hi : IntegrableOn g (Ici A) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      ((integrableOn_exp_mul_Ioi hr A).const_mul D)
  have hG' : IntegrableOn (fun t : ℝ => t ^ (-1 - (d : ℝ) / 2) *
      gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)) (Ici A) := by
    -- The model is integrable on every positive half-line.
    apply hi.mono'
    · exact ((measurable_id.pow_const _).mul
        ((contDiff_gaussianProfile u₀ u₂ γ 0).continuous.measurable.comp
          (measurable_const.mul measurable_id.sqrt))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      simpa only [Real.norm_eq_abs] using
        gaussian_time_profile_tail_pointwise_bound d u₀ u₂ γ C c ha hc hγ hl (hA.trans ht)
  refine ⟨hG', ?_⟩
  have H := setIntegral_mono_on hG'.abs hi measurableSet_Ici (fun t ht =>
    gaussian_time_profile_tail_pointwise_bound d u₀ u₂ γ C c ha hc hγ hl (hA.trans ht))
  apply H.trans_eq
  change (∫ t in Ici A, D * Real.exp ((-(c / 2) * lam ^ 2) * t)) = _
  rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_exp_mul_Ioi hr]
  dsimp only [D]
  rw [pow_add, show |lam| ^ 2 = lam ^ 2 by exact sq_abs lam]
  field_simp [hc.ne', hl₀]

/-- The Gaussian model tail has the required exponential decay at the common
logarithmic time cutoff, once the structural B is fixed sufficiently large. -/
theorem gaussian_time_profile_logarithmic_tail_bound (d : ℕ) (u₀ u₂ γ C c B : ℝ)
    (ha : |u₀| + |u₂| ≤ C) (hc : 0 < c) (hγ : c ≤ γ)
    (hB : 1 ≤ B) (hdecay : 4 ≤ c / 2 * B)
    {lam : ℝ} (hl : 0 < |lam|) (hs : |lam| ≤ Real.exp (-1)) :
    (∫ t in Ici (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))),
      |t ^ (-1 - (d : ℝ) / 2) * gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)|) ≤
      (2 * C * (1 + 2 / c) / c) * |lam| ^ d *
        Real.exp (-4 * Real.sqrt (Real.log (1 / |lam|))) := by
  have hL : 1 ≤ Real.sqrt (Real.log (1 / |lam|)) :=
    (Real.le_sqrt zero_le_one (zero_le_one.trans (one_le_log_inv_abs hl hs))).mpr
      (by simpa using one_le_log_inv_abs hl hs)
  have hA : 1 / |lam| ^ 2 ≤ B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|)) :=
    (div_le_div_of_nonneg_right hB (sq_nonneg _)).trans
      (le_mul_of_one_le_right (by positivity) hL)
  have H := (gaussian_time_profile_tail_integral_bound d u₀ u₂ γ C c ha hc hγ hl hA).2
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by
    have hC : 0 ≤ C := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans ha
    positivity)
  apply Real.exp_le_exp.mpr
  have he : -(c / 2) * lam ^ 2 *
      (B / |lam| ^ 2 * Real.sqrt (Real.log (1 / |lam|))) =
      -(c / 2 * B) * Real.sqrt (Real.log (1 / |lam|)) := by
    rw [sq_abs]
    field_simp [abs_pos.mp hl]
  rw [he]
  exact mul_le_mul_of_nonneg_right (neg_le_neg hdecay) (Real.sqrt_nonneg _)

end EinsteinFull
