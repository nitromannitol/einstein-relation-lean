import EinsteinFull.Calculus.CLSpatialDilation
import EinsteinFull.Calculus.CLRetainedDuhamelComparison
import EinsteinFull.Calculus.CLTransposeComparison
import EinsteinFull.Calculus.CLDeterministicPointKernel

/-! Deterministic retained comparisons and kernel bounds at every force. Forces
of norm above four are reduced to norm four by the spatial dilation with
`c = 4 / ‖ζ‖`, which keeps ellipticity and all smooth bounds; the resulting
powers of `‖ζ‖` are absorbed into `exp (‖ζ‖² t)` at times at least one. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ}

/-- A C¹ bound read through the contraction `x ↦ c⁻¹ • x`. -/
theorem clr_C1_dil_bound (w : Vec d → ℂ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (x : Vec d) :
    ‖w (c⁻¹ • x)‖ + Real.sqrt (∑ j, ‖fderiv ℝ (fun y => w (c⁻¹ • y)) x (unitVector j)‖ ^ 2) ≤
      c⁻¹ * (‖w (c⁻¹ • x)‖ +
        Real.sqrt (∑ j, ‖fderiv ℝ w (c⁻¹ • x) (unitVector j)‖ ^ 2)) := by
  have hfd : fderiv ℝ (fun y => w (c⁻¹ • y)) x = c⁻¹ • fderiv ℝ w (c⁻¹ • x) :=
    fderiv_comp_smul (f := w) c⁻¹
  have hci : 1 ≤ c⁻¹ := (one_le_inv₀ hc0).mpr hc1
  have hsum : (∑ j, ‖fderiv ℝ (fun y => w (c⁻¹ • y)) x (unitVector j)‖ ^ 2) =
      c⁻¹ ^ 2 * ∑ j, ‖fderiv ℝ w (c⁻¹ • x) (unitVector j)‖ ^ 2 := by
    rw [hfd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc0), mul_pow]
  rw [hsum, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h1 := norm_nonneg (w (c⁻¹ • x))
  have h2 := Real.sqrt_nonneg (∑ j, ‖fderiv ℝ w (c⁻¹ • x) (unitVector j)‖ ^ 2)
  nlinarith

/-- Powers of the force are absorbed into the Gaussian growth factor. -/
theorem clr_force_pow_le {z S : ℝ} (hz : 4 ≤ z) (hS : 1 ≤ S) (n : ℕ) :
    (z / 4) ^ n ≤ n.factorial * Real.exp (z ^ 2 * S) := by
  have h0 : 0 ≤ z / 4 := by linarith
  have h1 := Real.pow_div_factorial_le_exp _ h0 n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h2 : Real.exp (z / 4) ≤ Real.exp (z ^ 2 * S) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [div_le_iff₀ hf] at h1
  nlinarith [Real.exp_pos (z / 4)]

/-- The dilated prefactor and exponent in the original variables. -/
theorem clr_dil_prefactor {z S C₀ c₀ ρ F : ℝ} (d : ℕ) (hz : 4 < z) (hS : 1 ≤ S)
    (hC₀ : 0 ≤ C₀) (hF : 0 ≤ F) :
    (4 / z)⁻¹ * (C₀ * (2 + S / (4 / z) ^ 2) *
        Real.exp (C₀ * 4 ^ 2 * (S / (4 / z) ^ 2) - c₀ * (ρ / (4 / z)) ^ 2 / (S / (4 / z) ^ 2)) *
        (Real.sqrt |((4 / z) ^ d)⁻¹| * F)) ≤
      (C₀ * (d + 3).factorial) * (2 + S) *
        Real.exp ((C₀ + 1) * z ^ 2 * S - c₀ * ρ ^ 2 / S) * F := by
  have hz0 : 0 < z := by linarith
  have hS0 : 0 < S := by linarith
  set q : ℝ := z / 4 with hq
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  have hinv : (4 / z)⁻¹ = q := by rw [hq, inv_div]
  have hsq : S / (4 / z) ^ 2 = q ^ 2 * S := by rw [div_pow, div_div_eq_mul_div, hq]; ring
  have hexp : C₀ * 4 ^ 2 * (S / (4 / z) ^ 2) - c₀ * (ρ / (4 / z)) ^ 2 / (S / (4 / z) ^ 2) =
      C₀ * z ^ 2 * S - c₀ * ρ ^ 2 / S := by
    rw [hsq]
    have : ρ / (4 / z) = q * ρ := by rw [div_div_eq_mul_div, hq]; ring
    rw [this, hq]
    field_simp
  have habs : |((4 / z) ^ d)⁻¹| = q ^ d := by
    rw [← inv_pow, hinv, abs_of_nonneg (by positivity)]
  have hqd : Real.sqrt (q ^ d) ≤ q ^ d := by
    have h1 : 1 ≤ q ^ d := one_le_pow₀ hq1
    calc Real.sqrt (q ^ d) ≤ Real.sqrt (q ^ d) * Real.sqrt (q ^ d) :=
          le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr h1)
      _ = q ^ d := Real.mul_self_sqrt (by positivity)
  rw [hinv, hexp, hsq, habs]
  have hq2 : 2 + q ^ 2 * S ≤ q ^ 2 * (2 + S) := by
    have : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    nlinarith
  have hpow := clr_force_pow_le hz.le hS (d + 3)
  rw [← hq] at hpow
  have hE := Real.exp_pos (C₀ * z ^ 2 * S - c₀ * ρ ^ 2 / S)
  have hEE : Real.exp ((C₀ + 1) * z ^ 2 * S - c₀ * ρ ^ 2 / S) =
      Real.exp (z ^ 2 * S) * Real.exp (C₀ * z ^ 2 * S - c₀ * ρ ^ 2 / S) := by
    rw [← Real.exp_add]; ring_nf
  rw [hEE]
  calc q * (C₀ * (2 + q ^ 2 * S) * Real.exp (C₀ * z ^ 2 * S - c₀ * ρ ^ 2 / S) *
        (Real.sqrt (q ^ d) * F))
      ≤ q * (C₀ * (q ^ 2 * (2 + S)) * Real.exp (C₀ * z ^ 2 * S - c₀ * ρ ^ 2 / S) *
        (q ^ d * F)) := by gcongr
    _ = C₀ * q ^ (d + 3) * (2 + S) * Real.exp (C₀ * z ^ 2 * S - c₀ * ρ ^ 2 / S) * F := by ring
    _ ≤ C₀ * ((d + 3).factorial * Real.exp (z ^ 2 * S)) * (2 + S) *
        Real.exp (C₀ * z ^ 2 * S - c₀ * ρ ^ 2 / S) * F := by gcongr
    _ = _ := by ring

/-- A C¹ representative of a dilated class gives one of the class. -/
theorem clr_dil_transfer {c : ℝ} (hc0 : 0 < c) (u : Lp ℂ 2 (volume : Measure (Vec d)))
    {w : Vec d → ℂ} (hw : ContDiff ℝ 1 w)
    (hae : w =ᵐ[volume] (clrDil c hc0.ne' u : Vec d → ℂ)) :
    ContDiff ℝ 1 (fun x => w (c⁻¹ • x)) ∧
      (fun x => w (c⁻¹ • x)) =ᵐ[volume] (u : Vec d → ℂ) := by
  refine ⟨hw.comp (contDiff_const_smul _), ?_⟩
  have h1 := (clr_dil_qmp c⁻¹ (inv_ne_zero hc0.ne')).ae_eq_comp
    (hae.trans (clrDil_coe c hc0.ne' u))
  refine h1.trans (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]

theorem clr_dil_location {c ρ r : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {x z : Vec d}
    (hx : euclideanNorm (x - z) + 1 ≤ ρ / r) :
    euclideanNorm (c⁻¹ • x - c⁻¹ • z) + 1 ≤ ρ / c / r := by
  rw [← smul_sub, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hc0)]
  have hci : 1 ≤ c⁻¹ := (one_le_inv₀ hc0).mpr hc1
  have hn : 0 ≤ euclideanNorm (x - z) := Real.sqrt_nonneg _
  have h2 : c⁻¹ * euclideanNorm (x - z) ≤ c⁻¹ * (ρ / r - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : ρ / c / r = c⁻¹ * (ρ / r) := by ring
  rw [h3]
  nlinarith

theorem clr_dil_agree {c ρ : ℝ} (hc0 : 0 < c) {ω ω' : FieldPair d} {z : Vec d}
    (h : ∀ x, euclideanNorm (x - z) < ρ → ω'.1 x = ω.1 x) :
    ∀ y, euclideanNorm (y - c⁻¹ • z) < ρ / c →
      (scaleEnvironment c ω').1 y = (scaleEnvironment c ω).1 y := by
  intro y hy
  simp only [scaleEnvironment_matrix]
  apply h
  have : c • y - z = c • (y - c⁻¹ • z) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
  rw [this, TimeChange.euclideanNorm_smul, abs_of_pos hc0]
  rw [lt_div_iff₀ hc0] at hy
  linarith

theorem clr_dil_time {X : Type*} (T : ℝ≥0 → X) {c S : ℝ} (hc0 : 0 < c) (hS : 0 ≤ S) :
    T (⟨c ^ 2, sq_nonneg c⟩ * (S / c ^ 2).toNNReal) = T S.toNNReal := by
  congr 1
  apply NNReal.eq
  change c ^ 2 * ((S / c ^ 2).toNNReal : ℝ) = (S.toNNReal : ℝ)
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hS]
  field_simp

theorem clr_force_dil_norm {ζ : ℂ} (hζ : 4 < ‖ζ‖) : ‖((4 / ‖ζ‖ : ℝ) : ℂ) * ζ‖ = 4 := by
  have hz : 0 < ‖ζ‖ := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

/-- Pointwise C¹ comparison of two physical forward evolutions whose
coefficients agree on a ball, for every force and times at least one. -/
theorem clr_retained_pointwise_all (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M M' : ℕ → ℝ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 → IsSmoothWithBounds M' ω' →
    ∀ (i : Fin d) (ζ : ℂ),
    ∀ (P Pdag P' P'dag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ P' →
      IsPhysicalComplexTransposeSemigroup ω'.1 i ζ P' P'dag →
    ∀ (z : Vec d) (ρ : ℝ), 1 ≤ ρ →
      (∀ x, euclideanNorm (x - z) < ρ → ω'.1 x = ω.1 x) →
    ∀ (S : ℝ), 1 ≤ S → ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ w : Vec d → ℂ, ContDiff ℝ 1 w ∧
      w =ᵐ[volume] ((P' S.toNNReal f - P S.toNNReal f : Lp ℂ 2 (volume : Measure (Vec d))) :
        Vec d → ℂ) ∧
      ∀ x, euclideanNorm (x - z) + 1 ≤ ρ / 2 →
        ‖w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2) ≤
          C * (2 + S) * Real.exp (C * ‖ζ‖ ^ 2 * S - c * ρ ^ 2 / S) * ‖f‖ := by
  obtain ⟨C₀, c₀, hC₀, hc₀, h₀⟩ := clr_retained_pointwise d Λ hΛ M M'
  have hfac : (1 : ℝ) ≤ (d + 3).factorial := Nat.one_le_cast.mpr (Nat.factorial_pos _)
  set C : ℝ := C₀ * (d + 3).factorial + 1
  have hC₀C : C₀ ≤ C := by nlinarith
  refine ⟨C, c₀, by nlinarith, hc₀, ?_⟩
  intro ω ω' hell hsm hell' hsm' i ζ P Pdag P' P'dag hP hPdag hP' hP'dag z ρ hρ hagree S hS f
  have hS0 : 0 < S := by linarith
  have hf0 := norm_nonneg f
  rcases le_or_gt ‖ζ‖ 4 with hζ | hζ
  · obtain ⟨w, hw, hwae, hwb⟩ := h₀ ω ω' hell hsm hell' hsm' i ζ hζ P Pdag P' P'dag hP hPdag
      hP' hP'dag z ρ hρ hagree S hS f
    refine ⟨w, hw, hwae, fun x hx => (hwb x hx).trans ?_⟩
    have he : Real.exp (C₀ * ‖ζ‖ ^ 2 * S - c₀ * ρ ^ 2 / S) ≤
        Real.exp (C * ‖ζ‖ ^ 2 * S - c₀ * ρ ^ 2 / S) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hC₀C (mul_nonneg (sq_nonneg ‖ζ‖) hS0.le)
      nlinarith
    gcongr
  · have hz0 : 0 < ‖ζ‖ := by linarith
    set c : ℝ := 4 / ‖ζ‖ with hcdef
    have hc0 : 0 < c := by positivity
    have hc1 : c ≤ 1 := by rw [hcdef, div_le_one hz0]; linarith
    have habs : |c| ≤ 1 := by rw [abs_of_pos hc0]; exact hc1
    obtain ⟨hQ, hQdag⟩ := clr_physical_dilation c hc0.ne' hP hPdag
    obtain ⟨hQ', hQ'dag⟩ := clr_physical_dilation c hc0.ne' hP' hP'dag
    have hT : 1 ≤ S / c ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc1
      nlinarith
    have hρ' : 1 ≤ ρ / c := by rw [le_div_iff₀ hc0]; nlinarith
    obtain ⟨w, hw, hwae, hwb⟩ := h₀ (scaleEnvironment c ω) (scaleEnvironment c ω')
      (clr_isElliptic_scale c hell) (clr_isSmoothWithBounds_scale habs hsm)
      (clr_isElliptic_scale c hell') (clr_isSmoothWithBounds_scale habs hsm') i
      ((c : ℂ) * ζ) (clr_force_dil_norm hζ).le _ _ _ _ hQ hQdag hQ' hQ'dag (c⁻¹ • z) (ρ / c) hρ'
      (clr_dil_agree hc0 hagree) (S / c ^ 2) hT (clrDil c hc0.ne' f)
    have hdiff : (clrConj c hc0.ne' (fun s => P' (⟨c ^ 2, sq_nonneg c⟩ * s))
          (S / c ^ 2).toNNReal (clrDil c hc0.ne' f) -
        clrConj c hc0.ne' (fun s => P (⟨c ^ 2, sq_nonneg c⟩ * s))
          (S / c ^ 2).toNNReal (clrDil c hc0.ne' f)) =
        clrDil c hc0.ne' (P' S.toNNReal f - P S.toNNReal f) := by
      simp only [clrConj_apply, clrDil_inv_comp, clr_dil_time P' hc0 hS0.le,
        clr_dil_time P hc0 hS0.le, map_sub]
    rw [hdiff] at hwae
    obtain ⟨hwc, hwae'⟩ := clr_dil_transfer hc0 _ hw hwae
    refine ⟨fun x => w (c⁻¹ • x), hwc, hwae', fun x hx => ?_⟩
    have hy := clr_dil_location (r := 2) hc0 hc1 hx
    refine (clr_C1_dil_bound w hc0 hc1 x).trans ?_
    have hb := hwb (c⁻¹ • x) hy
    rw [clr_force_dil_norm hζ, clrDil_norm] at hb
    have hstep := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hc0).le
    refine hstep.trans ?_
    have hp := clr_dil_prefactor (C₀ := C₀) (c₀ := c₀) (ρ := ρ) (F := ‖f‖) d hζ hS
      (by linarith) hf0
    rw [← hcdef] at hp
    refine hp.trans ?_
    have he : Real.exp ((C₀ + 1) * ‖ζ‖ ^ 2 * S - c₀ * ρ ^ 2 / S) ≤
        Real.exp (C * ‖ζ‖ ^ 2 * S - c₀ * ρ ^ 2 / S) := by
      apply Real.exp_le_exp.mpr
      have h1 : C₀ + 1 ≤ C := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 (mul_nonneg (sq_nonneg ‖ζ‖) hS0.le)
      nlinarith
    have hK : C₀ * (d + 3).factorial ≤ C := by linarith
    gcongr


/-- Pointwise C¹ comparison of two physical transpose evolutions whose
coefficients agree on a ball, for every force and times at least one. -/
theorem clr_transpose_pointwise_all (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M M' : ℕ → ℝ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 → IsSmoothWithBounds M' ω' →
    ∀ (i : Fin d) (ζ : ℂ),
    ∀ (P Pdag P' P'dag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ P' →
      IsPhysicalComplexTransposeSemigroup ω'.1 i ζ P' P'dag →
    ∀ (z : Vec d) (ρ : ℝ), 1 ≤ ρ →
      (∀ x, euclideanNorm (x - z) < ρ → ω'.1 x = ω.1 x) →
    ∀ (S : ℝ), 1 ≤ S → ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ w : Vec d → ℂ, ContDiff ℝ 1 w ∧
      w =ᵐ[volume] ((P'dag S.toNNReal f - Pdag S.toNNReal f :
        Lp ℂ 2 (volume : Measure (Vec d))) :
        Vec d → ℂ) ∧
      ∀ x, euclideanNorm (x - z) + 1 ≤ ρ / 4 →
        ‖w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2) ≤
          C * (2 + S) * Real.exp (C * ‖ζ‖ ^ 2 * S - c * ρ ^ 2 / S) * ‖f‖ := by
  obtain ⟨C₀, c₀, hC₀, hc₀, h₀⟩ := clr_transpose_pointwise d Λ hΛ M M'
  have hfac : (1 : ℝ) ≤ (d + 3).factorial := Nat.one_le_cast.mpr (Nat.factorial_pos _)
  set C : ℝ := C₀ * (d + 3).factorial + 1
  have hC₀C : C₀ ≤ C := by nlinarith
  refine ⟨C, c₀, by nlinarith, hc₀, ?_⟩
  intro ω ω' hell hsm hell' hsm' i ζ P Pdag P' P'dag hP hPdag hP' hP'dag z ρ hρ hagree S hS f
  have hS0 : 0 < S := by linarith
  have hf0 := norm_nonneg f
  rcases le_or_gt ‖ζ‖ 4 with hζ | hζ
  · obtain ⟨w, hw, hwae, hwb⟩ := h₀ ω ω' hell hsm hell' hsm' i ζ hζ P Pdag P' P'dag hP hPdag
      hP' hP'dag z ρ hρ hagree S hS f
    refine ⟨w, hw, hwae, fun x hx => (hwb x hx).trans ?_⟩
    have he : Real.exp (C₀ * ‖ζ‖ ^ 2 * S - c₀ * ρ ^ 2 / S) ≤
        Real.exp (C * ‖ζ‖ ^ 2 * S - c₀ * ρ ^ 2 / S) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hC₀C (mul_nonneg (sq_nonneg ‖ζ‖) hS0.le)
      nlinarith
    gcongr
  · have hz0 : 0 < ‖ζ‖ := by linarith
    set c : ℝ := 4 / ‖ζ‖ with hcdef
    have hc0 : 0 < c := by positivity
    have hc1 : c ≤ 1 := by rw [hcdef, div_le_one hz0]; linarith
    have habs : |c| ≤ 1 := by rw [abs_of_pos hc0]; exact hc1
    obtain ⟨hQ, hQdag⟩ := clr_physical_dilation c hc0.ne' hP hPdag
    obtain ⟨hQ', hQ'dag⟩ := clr_physical_dilation c hc0.ne' hP' hP'dag
    have hT : 1 ≤ S / c ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc1
      nlinarith
    have hρ' : 1 ≤ ρ / c := by rw [le_div_iff₀ hc0]; nlinarith
    obtain ⟨w, hw, hwae, hwb⟩ := h₀ (scaleEnvironment c ω) (scaleEnvironment c ω')
      (clr_isElliptic_scale c hell) (clr_isSmoothWithBounds_scale habs hsm)
      (clr_isElliptic_scale c hell') (clr_isSmoothWithBounds_scale habs hsm') i
      ((c : ℂ) * ζ) (clr_force_dil_norm hζ).le _ _ _ _ hQ hQdag hQ' hQ'dag (c⁻¹ • z) (ρ / c) hρ'
      (clr_dil_agree hc0 hagree) (S / c ^ 2) hT (clrDil c hc0.ne' f)
    have hdiff : (clrConj c hc0.ne' (fun s => P'dag (⟨c ^ 2, sq_nonneg c⟩ * s))
          (S / c ^ 2).toNNReal (clrDil c hc0.ne' f) -
        clrConj c hc0.ne' (fun s => Pdag (⟨c ^ 2, sq_nonneg c⟩ * s))
          (S / c ^ 2).toNNReal (clrDil c hc0.ne' f)) =
        clrDil c hc0.ne' (P'dag S.toNNReal f - Pdag S.toNNReal f) := by
      simp only [clrConj_apply, clrDil_inv_comp, clr_dil_time P'dag hc0 hS0.le,
        clr_dil_time Pdag hc0 hS0.le, map_sub]
    rw [hdiff] at hwae
    obtain ⟨hwc, hwae'⟩ := clr_dil_transfer hc0 _ hw hwae
    refine ⟨fun x => w (c⁻¹ • x), hwc, hwae', fun x hx => ?_⟩
    have hy := clr_dil_location (r := 4) hc0 hc1 hx
    refine (clr_C1_dil_bound w hc0 hc1 x).trans ?_
    have hb := hwb (c⁻¹ • x) hy
    rw [clr_force_dil_norm hζ, clrDil_norm] at hb
    have hstep := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hc0).le
    refine hstep.trans ?_
    have hp := clr_dil_prefactor (C₀ := C₀) (c₀ := c₀) (ρ := ρ) (F := ‖f‖) d hζ hS
      (by linarith) hf0
    rw [← hcdef] at hp
    refine hp.trans ?_
    have he : Real.exp ((C₀ + 1) * ‖ζ‖ ^ 2 * S - c₀ * ρ ^ 2 / S) ≤
        Real.exp (C * ‖ζ‖ ^ 2 * S - c₀ * ρ ^ 2 / S) := by
      apply Real.exp_le_exp.mpr
      have h1 : C₀ + 1 ≤ C := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 (mul_nonneg (sq_nonneg ‖ζ‖) hS0.le)
      nlinarith
    have hK : C₀ * (d + 3).factorial ≤ C := by linarith
    gcongr


/-- The kernel of an evolution, from the kernel of its dilation at the rescaled time. -/
noncomputable def clrDilKernel (c : ℝ) (K : ℝ≥0 → Vec d → Vec d → ℂ) (t : ℝ≥0)
    (x y : Vec d) : ℂ :=
  ((|(c ^ d)⁻¹| : ℝ) : ℂ) * K ((t : ℝ) / c ^ 2).toNNReal (c⁻¹ • x) (c⁻¹ • y)

/-- Kernel representation under dilation, at one time. -/
theorem clr_dil_kernel_rep {c : ℝ} (hc0 : 0 < c) (L : Vec d → Vec d → ℂ)
    (f g : Lp ℂ 2 (volume : Measure (Vec d)))
    (hi : ∀ᵐ x ∂volume, Integrable (fun y => L x y * clrDil c hc0.ne' f y))
    (hr : (g : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, L x y * clrDil c hc0.ne' f y) :
    (∀ᵐ x ∂volume, Integrable
      (fun y => ((|(c ^ d)⁻¹| : ℝ) : ℂ) * L (c⁻¹ • x) (c⁻¹ • y) * f y)) ∧
    (clrDil c⁻¹ (inv_ne_zero hc0.ne') g : Vec d → ℂ) =ᵐ[volume]
      fun x => ∫ y, ((|(c ^ d)⁻¹| : ℝ) : ℂ) * L (c⁻¹ • x) (c⁻¹ • y) * f y := by
  have hq := clr_dil_qmp (d := d) c⁻¹ (inv_ne_zero hc0.ne')
  have hcf := clrDil_coe c hc0.ne' f
  have hint (x' : Vec d) : (∫ y, L x' y * clrDil c hc0.ne' f y) =
      ∫ y, ((|(c ^ d)⁻¹| : ℝ) : ℂ) * L x' (c⁻¹ • y) * f y := by
    have h1 : (∫ y, L x' y * clrDil c hc0.ne' f y) =
        ∫ y, (fun u => L x' (c⁻¹ • u) * f u) (c • y) := by
      apply integral_congr_ae
      filter_upwards [hcf] with y hy
      simp only [hy, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
    rw [h1]
    refine (clr_integral_dil c (fun u => L x' (c⁻¹ • u) * f u)).trans ?_
    rw [Complex.real_smul, ← integral_const_mul]
    congr 1; funext y; ring
  refine ⟨?_, ?_⟩
  · filter_upwards [hq.ae hi] with x hx
    have h2 : Integrable (fun y => L (c⁻¹ • x) y * f (c • y)) :=
      hx.congr (by filter_upwards [hcf] with y hy; rw [hy])
    have h3 := h2.comp_smul (inv_ne_zero hc0.ne')
    have h4 : Integrable (fun y => L (c⁻¹ • x) (c⁻¹ • y) * f y) := by
      simpa only [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul] using h3
    simpa only [mul_assoc] using h4.const_mul (((|(c ^ d)⁻¹| : ℝ) : ℂ))
  · have h5 := hq.ae_eq_comp hr
    filter_upwards [clrDil_coe c⁻¹ (inv_ne_zero hc0.ne') g, h5] with x h1 h2
    rw [h1]
    simp only [Function.comp_apply] at h2
    rw [h2, hint]

/-- The dilation kernel represents the original evolutions. -/
theorem clr_dilKernel_physical {c : ℝ} (hc0 : 0 < c)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))}
    {K : ℝ≥0 → Vec d → Vec d → ℂ}
    (hK : IsPhysicalComplexKernel (clrConj c hc0.ne' (fun s => P (⟨c ^ 2, sq_nonneg c⟩ * s)))
      (clrConj c hc0.ne' (fun s => Pdag (⟨c ^ 2, sq_nonneg c⟩ * s))) K) :
    IsPhysicalComplexKernel P Pdag (clrDilKernel c K) := by
  intro t ht f
  set s : ℝ≥0 := ((t : ℝ) / c ^ 2).toNNReal with hsdef
  have hs : 0 < s := by
    rw [hsdef, Real.toNNReal_pos]
    have : (0 : ℝ) < t := by exact_mod_cast ht
    positivity
  have hPt (T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) :
      clrDil c⁻¹ (inv_ne_zero hc0.ne')
        (clrConj c hc0.ne' (fun s => T (⟨c ^ 2, sq_nonneg c⟩ * s)) s (clrDil c hc0.ne' f)) =
        T t f := by
    simp only [clrConj_apply, clrDil_inv_comp]
    rw [hsdef, clr_dil_time T hc0 t.coe_nonneg, Real.toNNReal_coe]
  obtain ⟨⟨hi1, hr1⟩, ⟨hi2, hr2⟩⟩ := hK s hs (clrDil c hc0.ne' f)
  obtain ⟨h1, h2⟩ := clr_dil_kernel_rep hc0 (K s) f _ hi1 hr1
  obtain ⟨h3, h4⟩ := clr_dil_kernel_rep hc0 (fun x y => K s y x) f _ hi2 hr2
  rw [hPt P] at h2
  rw [hPt Pdag] at h4
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩


theorem clr_fderiv_scaled {g : Vec d → ℂ} {c : ℝ} {x : Vec d}
    (hg : DifferentiableAt ℝ g (c⁻¹ • x)) (k : ℂ) :
    fderiv ℝ (fun z => k * g (c⁻¹ • z)) x = k • c⁻¹ • fderiv ℝ g (c⁻¹ • x) := by
  have hd : DifferentiableAt ℝ (fun z => g (c⁻¹ • z)) x :=
    hg.comp x ((differentiableAt_id).const_smul c⁻¹)
  rw [fderiv_const_mul hd, fderiv_comp_smul (f := g) c⁻¹]

theorem clr_scaled_norm (k : ℂ) {c : ℝ} (hc0 : 0 < c) (L : Vec d →L[ℝ] ℂ) (v : Vec d) :
    ‖(k • c⁻¹ • L) v‖ = ‖k‖ * c⁻¹ * ‖L v‖ := by
  rw [smul_apply, smul_apply, norm_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc0), mul_assoc]

theorem clr_scaled_sqrt (k : ℂ) {c : ℝ} (hc0 : 0 < c) (L : Vec d →L[ℝ] ℂ) :
    Real.sqrt (∑ j : Fin d, ‖(k • c⁻¹ • L) (unitVector j)‖ ^ 2) =
      ‖k‖ * c⁻¹ * Real.sqrt (∑ j : Fin d, ‖L (unitVector j)‖ ^ 2) := by
  simp only [clr_scaled_norm k hc0, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), ← mul_pow,
    Real.sqrt_sq (by positivity)]

/-- Pointwise kernel bounds transfer through the dilation. -/
theorem clr_dil_kernel_pointwise {H : Vec d → Vec d → ℂ} {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hH : ContDiff ℝ 1 (fun z : Vec d × Vec d => H z.1 z.2)) (k : ℂ) (x y : Vec d) :
    ‖k * H (c⁻¹ • x) (c⁻¹ • y)‖ +
      Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => k * H (c⁻¹ • z) (c⁻¹ • y)) x (unitVector j)‖ ^ 2) +
      Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => k * H (c⁻¹ • x) (c⁻¹ • z)) y (unitVector j)‖ ^ 2) ≤
    ‖k‖ * c⁻¹ * (‖H (c⁻¹ • x) (c⁻¹ • y)‖ +
      Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => H z (c⁻¹ • y)) (c⁻¹ • x) (unitVector j)‖ ^ 2) +
      Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => H (c⁻¹ • x) z) (c⁻¹ • y) (unitVector j)‖ ^ 2)) := by
  have h1 : ∀ y', Differentiable ℝ (fun z => H z y') := fun y' =>
    (hH.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero
  have h2 : ∀ x', Differentiable ℝ (fun z => H x' z) := fun x' =>
    (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
  rw [clr_fderiv_scaled ((h1 _) _) k, clr_fderiv_scaled ((h2 _) _) k, clr_scaled_sqrt k hc0,
    clr_scaled_sqrt k hc0, norm_mul]
  have hci : 1 ≤ c⁻¹ := (one_le_inv₀ hc0).mpr hc1
  have hn := norm_nonneg (H (c⁻¹ • x) (c⁻¹ • y))
  have hk := norm_nonneg k
  have : ‖k‖ * ‖H (c⁻¹ • x) (c⁻¹ • y)‖ ≤ ‖k‖ * c⁻¹ * ‖H (c⁻¹ • x) (c⁻¹ • y)‖ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hn hci) hk
  nlinarith


/-- The integral-operator clause of the kernel bounds transfers through the dilation. -/
theorem clr_dil_kernel_operator {H : Vec d → Vec d → ℂ} {c A : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hH : ContDiff ℝ 1 (fun z : Vec d × Vec d => H z.1 z.2))
    (hop : ∀ (f : Vec d → ℂ) (B : ℝ), 0 ≤ B →
      AEStronglyMeasurable f volume → (∀ᵐ y ∂volume, ‖f y‖ ≤ B) →
      let u := fun x => ∫ y, H x y * f y
      Differentiable ℝ u ∧ ∀ x : Vec d,
        Integrable (fun y => H x y * f y) ∧
        (∀ j : Fin d,
          Integrable (fun y => fderiv ℝ (fun z => H z y) x (unitVector j) * f y) ∧
          fderiv ℝ u x (unitVector j) =
            ∫ y, fderiv ℝ (fun z => H z y) x (unitVector j) * f y) ∧
        ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * B)
    (f : Vec d → ℂ) (B : ℝ) (hB : 0 ≤ B) (hfm : AEStronglyMeasurable f volume)
    (hfB : ∀ᵐ y ∂volume, ‖f y‖ ≤ B) :
    let k : ℂ := ((|(c ^ d)⁻¹| : ℝ) : ℂ)
    let u := fun x => ∫ y, k * H (c⁻¹ • x) (c⁻¹ • y) * f y
    Differentiable ℝ u ∧ ∀ x : Vec d,
      Integrable (fun y => k * H (c⁻¹ • x) (c⁻¹ • y) * f y) ∧
      (∀ j : Fin d,
        Integrable (fun y =>
          fderiv ℝ (fun z => k * H (c⁻¹ • z) (c⁻¹ • y)) x (unitVector j) * f y) ∧
        fderiv ℝ u x (unitVector j) =
          ∫ y, fderiv ℝ (fun z => k * H (c⁻¹ • z) (c⁻¹ • y)) x (unitVector j) * f y) ∧
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ c⁻¹ * A * B := by
  intro k u
  have hq := clr_dil_qmp (d := d) c hc0.ne'
  set g : Vec d → ℂ := fun y => f (c • y) with hgdef
  have hgm : AEStronglyMeasurable g volume := hfm.comp_quasiMeasurePreserving hq
  have hgB : ∀ᵐ y ∂volume, ‖g y‖ ≤ B := hq.ae hfB
  have hop' := hop g B hB hgm hgB
  dsimp only at hop'
  obtain ⟨hdiff, hx⟩ := hop'
  set ũ : Vec d → ℂ := fun x => ∫ y, H x y * g y with hũ
  have hcv (F : Vec d → ℂ) : (∫ y, F y * g y) = k * ∫ y, F (c⁻¹ • y) * f y := by
    have h := clr_integral_dil c (fun y => F (c⁻¹ • y) * f y)
    simp only [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul] at h
    rw [hgdef, h, Complex.real_smul]
  have hu : u = fun x => ũ (c⁻¹ • x) := by
    funext x
    simp only [u, hũ, hcv (H (c⁻¹ • x)), mul_assoc, integral_const_mul]
  have hdx (y : Vec d) (x : Vec d) :
      fderiv ℝ (fun z => k * H (c⁻¹ • z) (c⁻¹ • y)) x =
        k • c⁻¹ • fderiv ℝ (fun z => H z (c⁻¹ • y)) (c⁻¹ • x) :=
    clr_fderiv_scaled (((hH.comp (contDiff_id.prodMk contDiff_const)).differentiable
      one_ne_zero) _) k
  have hint (F : Vec d → ℂ) (hF : Integrable (fun y => F y * g y)) (a : ℂ) :
      Integrable (fun y => a * (F (c⁻¹ • y) * f y)) := by
    have h3 := hF.comp_smul (inv_ne_zero hc0.ne')
    simp only [hgdef, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul] at h3
    exact h3.const_mul a
  refine ⟨?_, fun x => ?_⟩
  · rw [hu]
    exact hdiff.comp (differentiable_id.const_smul c⁻¹)
  · obtain ⟨hi, hj, hb⟩ := hx (c⁻¹ • x)
    refine ⟨?_, fun j => ⟨?_, ?_⟩, ?_⟩
    · simpa only [mul_assoc] using hint (H (c⁻¹ • x)) hi k
    · simp only [hdx, smul_apply, smul_eq_mul, Complex.real_smul]
      have := hint (fun y' => fderiv ℝ (fun z => H z y') (c⁻¹ • x) (unitVector j)) (hj j).1
        (k * ((c⁻¹ : ℝ) : ℂ))
      simpa only [mul_assoc] using this
    · rw [hu, fderiv_comp_smul (f := ũ) c⁻¹, smul_apply, (hj j).2,
        hcv (fun y' => fderiv ℝ (fun z => H z y') (c⁻¹ • x) (unitVector j))]
      simp only [hdx, smul_apply, smul_eq_mul, Complex.real_smul]
      rw [← integral_const_mul, ← integral_const_mul]
      congr 1; funext y; ring
    · rw [hu]
      refine (clr_C1_dil_bound ũ hc0 hc1 x).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hb (inv_pos.mpr hc0).le


/-- The kernel prefactor of the dilation in the original variables. -/
theorem clr_kernel_prefactor {z t C₀ c₀ e F : ℝ} (d N₀ : ℕ) (hz : 4 < z) (ht : 1 ≤ t)
    (hC₀ : 0 ≤ C₀) (hF : 0 ≤ F) :
    (z / 4) ^ d * (z / 4) * (C₀ * (2 + (z / 4) ^ 2 * t) ^ N₀ *
        Real.exp (C₀ * 4 ^ 2 * ((z / 4) ^ 2 * t) -
          c₀ * ((z / 4) * e) ^ 2 / ((z / 4) ^ 2 * t))) * F ≤
      (C₀ * (d + 1 + 2 * N₀).factorial) * (2 + t) ^ N₀ *
        Real.exp ((C₀ + 1) * z ^ 2 * t - c₀ * e ^ 2 / t) * F := by
  set q : ℝ := z / 4 with hq
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  have hq0 : 0 < q := by linarith
  have ht0 : 0 < t := by linarith
  have hexp : C₀ * 4 ^ 2 * (q ^ 2 * t) - c₀ * (q * e) ^ 2 / (q ^ 2 * t) =
      C₀ * z ^ 2 * t - c₀ * e ^ 2 / t := by
    rw [hq]; field_simp
  rw [hexp]
  have h2 : 2 + q ^ 2 * t ≤ q ^ 2 * (2 + t) := by
    have : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    nlinarith
  have hpow := clr_force_pow_le hz.le ht (d + 1 + 2 * N₀)
  rw [← hq] at hpow
  have hEE : Real.exp ((C₀ + 1) * z ^ 2 * t - c₀ * e ^ 2 / t) =
      Real.exp (z ^ 2 * t) * Real.exp (C₀ * z ^ 2 * t - c₀ * e ^ 2 / t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hEE]
  calc q ^ d * q * (C₀ * (2 + q ^ 2 * t) ^ N₀ * Real.exp (C₀ * z ^ 2 * t - c₀ * e ^ 2 / t)) * F
      ≤ q ^ d * q * (C₀ * (q ^ 2 * (2 + t)) ^ N₀ *
          Real.exp (C₀ * z ^ 2 * t - c₀ * e ^ 2 / t)) * F := by gcongr
    _ = C₀ * q ^ (d + 1 + 2 * N₀) * (2 + t) ^ N₀ *
          Real.exp (C₀ * z ^ 2 * t - c₀ * e ^ 2 / t) * F := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ C₀ * ((d + 1 + 2 * N₀).factorial * Real.exp (z ^ 2 * t)) * (2 + t) ^ N₀ *
          Real.exp (C₀ * z ^ 2 * t - c₀ * e ^ 2 / t) * F := by gcongr
    _ = _ := by ring

theorem clr_shape_exp_mono {K C c t z e : ℝ} {N : ℕ} (hK : K ≤ C) (hK0 : 0 ≤ K) (ht : 0 ≤ t)
    (hz : 0 ≤ z) :
    K * (2 + t) ^ N * Real.exp (K * z * t - c * e) ≤
      C * (2 + t) ^ N * Real.exp (C * z * t - c * e) := by
  have h1 : Real.exp (K * z * t - c * e) ≤ Real.exp (C * z * t - c * e) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hK (mul_nonneg hz ht)
    nlinarith
  have hC0 : 0 ≤ C := hK0.trans hK
  gcongr

/-- Deterministic point-kernel bounds at all times at least one, for every force. -/
theorem clr_det_point_kernel_unit_all (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M : ℕ → ℝ) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (env : FieldPair d), IsElliptic Λ env.1 → IsSmoothWithBounds M env →
    ∀ (i : Fin d) (ζ : ℂ),
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup env.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup env.1 i ζ P Pdag →
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
      IsPhysicalComplexKernel P Pdag K ∧
      ∀ H ∈ [K, fun t x y => K t y x], ∀ (t : ℝ≥0), 1 ≤ (t : ℝ) →
        ContDiff ℝ 1 (fun z : Vec d × Vec d => H t z.1 z.2) ∧
        (∀ x y : Vec d,
          ‖H t x y‖ +
            Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ (fun z => H t z y) x (unitVector j)‖ ^ 2) +
            Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ (fun z => H t x z) y (unitVector j)‖ ^ 2) ≤
          C * (2 + (t : ℝ)) ^ N *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) -
              c * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
        (∀ (f : Vec d → ℂ) (B : ℝ), 0 ≤ B →
          AEStronglyMeasurable f volume → (∀ᵐ y ∂volume, ‖f y‖ ≤ B) →
          let u := fun x => ∫ y, H t x y * f y
          Differentiable ℝ u ∧ ∀ x : Vec d,
            Integrable (fun y => H t x y * f y) ∧
            (∀ j : Fin d,
              Integrable (fun y =>
                fderiv ℝ (fun z => H t z y) x (unitVector j) * f y) ∧
              fderiv ℝ u x (unitVector j) =
                ∫ y, fderiv ℝ (fun z => H t z y) x (unitVector j) * f y) ∧
            ‖u x‖ + Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
              C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B) := by
  obtain ⟨C₀, c₀, N₀, hC₀, hc₀, h₀⟩ := clr_det_point_kernel_unit d hd Λ hΛ M
  have hfac : (1 : ℝ) ≤ (d + 1 + 2 * N₀).factorial :=
    Nat.one_le_cast.mpr (Nat.factorial_pos _)
  set C : ℝ := C₀ * (d + 1 + 2 * N₀).factorial + 1 with hCdef
  have hC₀C : C₀ ≤ C := by nlinarith
  have hC₁C : C₀ + 1 ≤ C := by nlinarith
  have hKC : C₀ * (d + 1 + 2 * N₀).factorial ≤ C := by linarith
  refine ⟨C, c₀, N₀, by linarith, hc₀, ?_⟩
  intro env hell hsm i ζ P Pdag hP hPdag
  have hz2 : 0 ≤ ‖ζ‖ ^ 2 := sq_nonneg _
  rcases le_or_gt ‖ζ‖ 4 with hζ | hζ
  · obtain ⟨K, hK, hb⟩ := h₀ env hell hsm i ζ hζ P Pdag hP hPdag
    refine ⟨K, hK, fun H hH t ht => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hb H hH t ht
    refine ⟨h1, fun x y => (h2 x y).trans ?_, fun f B hB hfm hfB => ?_⟩
    · have := clr_shape_exp_mono (N := N₀) (c := c₀)
        (e := euclideanNorm (x - y) ^ 2 / (t : ℝ)) hC₀C (by linarith) t.coe_nonneg hz2
      simpa only [mul_div_assoc] using this
    · have h3' := h3 f B hB hfm hfB
      dsimp only at h3' ⊢
      obtain ⟨ha, hb'⟩ := h3'
      refine ⟨ha, fun x => ?_⟩
      obtain ⟨b1, b2, b3⟩ := hb' x
      refine ⟨b1, b2, b3.trans ?_⟩
      have := clr_shape_exp_mono (N := N₀) (c := 0) (e := 0) hC₀C (by linarith)
        t.coe_nonneg hz2
      simp only [zero_mul, sub_zero] at this
      exact mul_le_mul_of_nonneg_right this hB
  · have hz0 : 0 < ‖ζ‖ := by linarith
    set c : ℝ := 4 / ‖ζ‖ with hcdef
    have hc0 : 0 < c := by positivity
    have hc1 : c ≤ 1 := by rw [hcdef, div_le_one hz0]; linarith
    have habs : |c| ≤ 1 := by rw [abs_of_pos hc0]; exact hc1
    have hcinv : c⁻¹ = ‖ζ‖ / 4 := by rw [hcdef, inv_div]
    obtain ⟨hQ, hQdag⟩ := clr_physical_dilation c hc0.ne' hP hPdag
    obtain ⟨K, hK, hb⟩ := h₀ (scaleEnvironment c env) (clr_isElliptic_scale c hell)
      (clr_isSmoothWithBounds_scale habs hsm) i ((c : ℂ) * ζ) (clr_force_dil_norm hζ).le _ _
      hQ hQdag
    refine ⟨clrDilKernel c K, clr_dilKernel_physical hc0 hK, fun H hH t ht => ?_⟩
    set s : ℝ≥0 := ((t : ℝ) / c ^ 2).toNNReal with hsdef
    have hs : (s : ℝ) = (‖ζ‖ / 4) ^ 2 * t := by
      rw [hsdef, Real.coe_toNNReal _ (by positivity), ← hcinv]
      field_simp
    have hs1 : 1 ≤ (s : ℝ) := by
      rw [hs]
      have : 1 ≤ (‖ζ‖ / 4) ^ 2 := one_le_pow₀ (by linarith)
      nlinarith
    have hk : ‖(((|(c ^ d)⁻¹| : ℝ)) : ℂ)‖ = (‖ζ‖ / 4) ^ d := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_abs, ← inv_pow, hcinv,
        abs_of_nonneg (by positivity)]
    have hk' : |(c ^ d)⁻¹| = (‖ζ‖ / 4) ^ d := by
      rw [← inv_pow, hcinv, abs_of_nonneg (by positivity)]
    obtain ⟨H', hH', hHeq⟩ : ∃ H' ∈ [K, fun t x y => K t y x],
        H t = fun x y => (((|(c ^ d)⁻¹| : ℝ)) : ℂ) * H' s (c⁻¹ • x) (c⁻¹ • y) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hH
      rcases hH with rfl | rfl
      · exact ⟨K, by simp, rfl⟩
      · exact ⟨fun t x y => K t y x, by simp, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hb H' hH' s hs1
    simp only [hHeq]
    refine ⟨?_, fun x y => ?_, fun f B hB hfm hfB => ?_⟩
    · exact contDiff_const.mul (h1.comp ((contDiff_fst.const_smul c⁻¹).prodMk
        (contDiff_snd.const_smul c⁻¹)))
    · refine (clr_dil_kernel_pointwise hc0 hc1 h1 _ x y).trans ?_
      have hb2 := h2 (c⁻¹ • x) (c⁻¹ • y)
      rw [← smul_sub, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hc0),
        clr_force_dil_norm hζ, hs, hcinv] at hb2
      rw [hk, hcinv]
      have hstep := mul_le_mul_of_nonneg_left hb2
        (by positivity : (0 : ℝ) ≤ (‖ζ‖ / 4) ^ d * (‖ζ‖ / 4))
      have hp := clr_kernel_prefactor (C₀ := C₀) (c₀ := c₀) (e := euclideanNorm (x - y))
        (F := 1) d N₀ hζ ht (by linarith) zero_le_one
      simp only [mul_one] at hp
      refine hstep.trans (hp.trans ?_)
      calc C₀ * ((d + 1 + 2 * N₀).factorial : ℝ) * (2 + (t : ℝ)) ^ N₀ *
            Real.exp ((C₀ + 1) * ‖ζ‖ ^ 2 * t - c₀ * euclideanNorm (x - y) ^ 2 / t)
          ≤ C * (2 + (t : ℝ)) ^ N₀ *
            Real.exp ((C₀ + 1) * ‖ζ‖ ^ 2 * t - c₀ * euclideanNorm (x - y) ^ 2 / t) := by
            gcongr
        _ ≤ C * (2 + (t : ℝ)) ^ N₀ *
            Real.exp (C * ‖ζ‖ ^ 2 * t - c₀ * euclideanNorm (x - y) ^ 2 / t) := by
            gcongr
    · have hop := clr_dil_kernel_operator hc0 hc1 h1 h3 f B hB hfm hfB
      dsimp only at hop ⊢
      obtain ⟨ha, hb'⟩ := hop
      refine ⟨ha, fun x => ?_⟩
      obtain ⟨b1, b2, b3⟩ := hb' x
      refine ⟨b1, b2, b3.trans ?_⟩
      rw [clr_force_dil_norm hζ, hs, hcinv]
      have hp := clr_kernel_prefactor (C₀ := C₀) (c₀ := 0) (e := 0) (F := B) d N₀ hζ ht
        (by linarith) hB
      simp only [mul_zero, zero_mul, zero_div, sub_zero] at hp
      have hqd : 1 ≤ (‖ζ‖ / 4) ^ d := one_le_pow₀ (by linarith)
      have hA : 0 ≤ ‖ζ‖ / 4 * (C₀ * (2 + (‖ζ‖ / 4) ^ 2 * (t : ℝ)) ^ N₀ *
          Real.exp (C₀ * 4 ^ 2 * ((‖ζ‖ / 4) ^ 2 * t))) * B := by positivity
      calc ‖ζ‖ / 4 * (C₀ * (2 + (‖ζ‖ / 4) ^ 2 * (t : ℝ)) ^ N₀ *
            Real.exp (C₀ * 4 ^ 2 * ((‖ζ‖ / 4) ^ 2 * t))) * B
          ≤ (‖ζ‖ / 4) ^ d * (‖ζ‖ / 4 * (C₀ * (2 + (‖ζ‖ / 4) ^ 2 * (t : ℝ)) ^ N₀ *
            Real.exp (C₀ * 4 ^ 2 * ((‖ζ‖ / 4) ^ 2 * t))) * B) := le_mul_of_one_le_left hA hqd
        _ = (‖ζ‖ / 4) ^ d * (‖ζ‖ / 4) * (C₀ * (2 + (‖ζ‖ / 4) ^ 2 * (t : ℝ)) ^ N₀ *
            Real.exp (C₀ * 4 ^ 2 * ((‖ζ‖ / 4) ^ 2 * t))) * B := by ring
        _ ≤ C₀ * ((d + 1 + 2 * N₀).factorial : ℝ) * (2 + (t : ℝ)) ^ N₀ *
            Real.exp ((C₀ + 1) * ‖ζ‖ ^ 2 * t) * B := hp
        _ ≤ C * (2 + (t : ℝ)) ^ N₀ * Real.exp (C * ‖ζ‖ ^ 2 * t) * B := by
            gcongr


end EinsteinFull
