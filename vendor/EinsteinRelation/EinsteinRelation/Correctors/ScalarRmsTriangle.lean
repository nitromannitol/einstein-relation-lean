import EinsteinRelation.External.AKMLocalCorrectors
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM

/-- Cauchy-Schwarz inequality for integrals w.r.t. a finite measure. -/
lemma cauchy_schwarz_integral {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν]
    {f g : Ω → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, (f x)^2 ∂ν) * (∫ x, (g x)^2 ∂ν) := by
  have hfsq : Integrable (fun x => (f x)^2) ν := hf.integrable_sq
  have hgsq : Integrable (fun x => (g x)^2) ν := hg.integrable_sq
  have hfg : Integrable (fun x => f x * g x) ν := hf.integrable_mul hg
  have h_nonneg_quad : ∀ t : ℝ, 0 ≤ (∫ x, (f x - t * g x)^2 ∂ν) := by
    intro t; apply integral_nonneg; intro x; apply pow_two_nonneg
  have h_expand : ∀ t : ℝ, (∫ x, (f x - t * g x)^2 ∂ν) =
      (∫ x, (f x)^2 ∂ν) - 2*t*(∫ x, f x * g x ∂ν) + t^2*(∫ x, (g x)^2 ∂ν) := by
    intro t
    have h_int1 : Integrable (fun x => (f x)^2 - 2*t*(f x * g x)) ν := hfsq.sub (hfg.const_mul (2*t))
    have h_int2 : Integrable (fun x => t^2*(g x)^2) ν := hgsq.const_mul (t^2)
    calc
      (∫ x, (f x - t * g x)^2 ∂ν) = (∫ x, (f x)^2 - 2*t*(f x * g x) + t^2*(g x)^2 ∂ν) := by
        refine integral_congr_ae ?_; filter_upwards with x; ring
      _ = (∫ x, ((f x)^2 - 2*t*(f x * g x)) + (t^2*(g x)^2) ∂ν) := by ring
      _ = (∫ x, (f x)^2 - 2*t*(f x * g x) ∂ν) + (∫ x, t^2*(g x)^2 ∂ν) := by
        rw [integral_add h_int1 h_int2]
      _ = ((∫ x, (f x)^2 ∂ν) - (∫ x, 2*t*(f x * g x) ∂ν)) + (∫ x, t^2*(g x)^2 ∂ν) := by
        rw [integral_sub hfsq (hfg.const_mul (2*t))]
      _ = ((∫ x, (f x)^2 ∂ν) - 2*t*(∫ x, f x * g x ∂ν)) + t^2*(∫ x, (g x)^2 ∂ν) := by
        simp [integral_const_mul]
      _ = (∫ x, (f x)^2 ∂ν) - 2*t*(∫ x, f x * g x ∂ν) + t^2*(∫ x, (g x)^2 ∂ν) := by ring
  set If := ∫ x, (f x)^2 ∂ν
  set Ig := ∫ x, (g x)^2 ∂ν
  set Ifg := ∫ x, f x * g x ∂ν
  have hIf_nonneg : 0 ≤ If := integral_nonneg (fun x => pow_two_nonneg _)
  have hIg_nonneg : 0 ≤ Ig := integral_nonneg (fun x => pow_two_nonneg _)
  by_cases hIg_zero : Ig = 0
  · have hg_sq_zero_ae : (fun x => (g x)^2) =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => pow_two_nonneg _) hgsq).mp hIg_zero
    have hfg_zero_ae : (fun x => f x * g x) =ᵐ[ν] 0 := by
      filter_upwards [hg_sq_zero_ae] with x hx
      have hgx : g x = 0 := by
        have : (g x)^2 = 0 := by simpa using hx
        nlinarith
      simp [hgx]
    have hIfg_zero : Ifg = 0 := by
      dsimp [Ifg]
      calc
        (∫ x, f x * g x ∂ν) = (∫ x, (0 : ℝ) ∂ν) := integral_congr_ae hfg_zero_ae
        _ = 0 := by simp
    rw [hIfg_zero, hIg_zero]; simp
  · set t := Ifg / Ig with ht
    have h_min := h_nonneg_quad t
    rw [h_expand t, ht] at h_min
    field_simp [hIg_zero] at h_min
    nlinarith

/-- Source: `paper/main.tex:693–698`. Normalized L² oscillations obey
the triangle inequality on every finite-measure spatial domain. -/
theorem scalarRms_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Set Ω) [IsFiniteMeasure (μ.restrict U)]
    {f g : Ω → ℝ} (hf : MemLp f 2 (μ.restrict U))
    (hg : MemLp g 2 (μ.restrict U)) :
    scalarRms μ U (fun x => f x - g x) ≤ scalarRms μ U f + scalarRms μ U g := by
  unfold scalarRms
  have h_avg_fg : ⨍ x in U, ((f x - g x))^2 ∂μ = (μ.real U)⁻¹ • ∫ x in U, ((f x - g x))^2 ∂μ :=
    setAverage_eq (μ := μ) (fun x => ((f x - g x))^2) U
  have h_avg_f : ⨍ x in U, (f x)^2 ∂μ = (μ.real U)⁻¹ • ∫ x in U, (f x)^2 ∂μ :=
    setAverage_eq (μ := μ) (fun x => (f x)^2) U
  have h_avg_g : ⨍ x in U, (g x)^2 ∂μ = (μ.real U)⁻¹ • ∫ x in U, (g x)^2 ∂μ :=
    setAverage_eq (μ := μ) (fun x => (g x)^2) U
  rw [h_avg_fg, h_avg_f, h_avg_g]
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
  set a := (μ.real U)⁻¹ with ha
  set If := ∫ x in U, (f x)^2 ∂μ with hIf
  set Ig := ∫ x in U, (g x)^2 ∂μ with hIg
  set Ifg := ∫ x in U, f x * g x ∂μ with hIfg
  have hIf_nonneg : 0 ≤ If := integral_nonneg (fun x => pow_two_nonneg _)
  have hIg_nonneg : 0 ≤ Ig := integral_nonneg (fun x => pow_two_nonneg _)
  have ha_nonneg : 0 ≤ a := inv_nonneg.mpr measureReal_nonneg
  -- Key expansion: ∫ (f-g)^2 = ∫ f^2 + ∫ g^2 - 2∫ fg  (all over U)
  have h_expand' : If + Ig - 2*Ifg = ∫ x in U, ((f x - g x))^2 ∂μ := by
    rw [hIf, hIg, hIfg]
    calc
      (∫ x in U, (f x)^2 ∂μ) + (∫ x in U, (g x)^2 ∂μ) - 2*(∫ x in U, f x * g x ∂μ) =
          ((∫ x in U, (f x)^2 ∂μ) - 2*(∫ x in U, f x * g x ∂μ)) + (∫ x in U, (g x)^2 ∂μ) := by ring
      _ = ((∫ x in U, (f x)^2 ∂μ) - (∫ x in U, 2*(f x * g x) ∂μ)) + (∫ x in U, (g x)^2 ∂μ) := by
        simp [integral_const_mul]
      _ = (∫ x in U, ((f x)^2 - 2*(f x * g x)) ∂μ) + (∫ x in U, (g x)^2 ∂μ) := by
        have hsub := (integral_sub (f := fun x => (f x)^2) (g := fun x => 2*(f x * g x))
          (hf.integrable_sq) ((hf.integrable_mul hg).const_mul 2)).symm
        -- hsub : (∫ f^2) - (∫ 2*(f*g)) = ∫ (f^2 - 2*(f*g))
        rw [hsub]
      _ = ∫ x in U, (((f x)^2 - 2*(f x * g x)) + (g x)^2) ∂μ := by
        have hadd := (integral_add (f := fun x => (f x)^2 - 2*(f x * g x)) (g := fun x => (g x)^2)
          (hf.integrable_sq.sub ((hf.integrable_mul hg).const_mul 2)) (hg.integrable_sq)).symm
        -- hadd : (∫ (f^2 - 2*(f*g))) + (∫ g^2) = ∫ ((f^2 - 2*(f*g)) + g^2)
        rw [hadd]
      _ = ∫ x in U, ((f x)^2 - 2*(f x * g x) + (g x)^2) ∂μ := rfl
      _ = ∫ x in U, ((f x - g x))^2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with x
        ring
  rw [← h_expand']
  -- Goal: Real.sqrt (a * (If + Ig - 2*Ifg)) ≤ Real.sqrt (a * If) + Real.sqrt (a * Ig)
  by_cases ha0 : a = 0
  · simp [ha0]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha0)
    have h_sqrt_mul : ∀ (x : ℝ), 0 ≤ x → Real.sqrt (a * x) = Real.sqrt a * Real.sqrt x := by
      intro x hx; rw [Real.sqrt_mul ha_nonneg]
    have h_sum_nonneg : 0 ≤ If + Ig - 2*Ifg := by
      rw [h_expand']
      refine integral_nonneg ?_
      intro x
      apply pow_two_nonneg
    rw [h_sqrt_mul (If + Ig - 2*Ifg) h_sum_nonneg,
      h_sqrt_mul If hIf_nonneg,
      h_sqrt_mul Ig hIg_nonneg,
      ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    -- Need: Real.sqrt (If + Ig - 2*Ifg) ≤ Real.sqrt If + Real.sqrt Ig
    have h_cauchy : Ifg ^ 2 ≤ If * Ig := by
      rw [hIf, hIg, hIfg]
      simpa using cauchy_schwarz_integral hf hg
    have h_ifg_ge : -Real.sqrt (If * Ig) ≤ Ifg := by
      have h_abs : |Ifg| ≤ Real.sqrt (If * Ig) := Real.abs_le_sqrt h_cauchy
      linarith [abs_le.mp h_abs]
    have h_sqrt_sum_nonneg : 0 ≤ Real.sqrt If + Real.sqrt Ig :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_sq_ineq : (Real.sqrt (If + Ig - 2*Ifg))^2 ≤ (Real.sqrt If + Real.sqrt Ig)^2 := by
      rw [Real.sq_sqrt h_sum_nonneg]
      rw [add_sq, Real.sq_sqrt hIf_nonneg, Real.sq_sqrt hIg_nonneg]
      -- Goal: If + Ig - 2*Ifg ≤ If + 2*√If*√Ig + Ig
      -- Simplify: -2*Ifg ≤ 2*√If*√Ig, i.e., -Ifg ≤ √If*√Ig = √(If*Ig)
      have h_sqrt_mul : Real.sqrt (If * Ig) = Real.sqrt If * Real.sqrt Ig := by
        rw [Real.sqrt_mul hIf_nonneg]
      have h : -Ifg ≤ Real.sqrt If * Real.sqrt Ig := by
        rw [← h_sqrt_mul]
        linarith
      nlinarith
    nlinarith
end EinsteinRelation.Correctors
