import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Source: `paper/main.tex:832–840`. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

/-- Weighted AM-GM: `u^p * v^(1-p) ≤ p * u + (1-p) * v` for nonnegative `u, v`. -/
theorem rpow_mul_rpow_le_weighted_add_aux {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ p * v ^ (1 - p) ≤ p * u + (1 - p) * v :=
  Real.geom_mean_le_arith_mean2_weighted hp0.le (sub_nonneg.mpr hp1.le) hu hv (by ring)

theorem integrable_rpow_mul_rpow_of_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => (f x)^p * (g x)^(1-p)) μ := by
  refine Integrable.mono' ((hf.const_mul p).add (hg.const_mul (1 - p))) ?_ ?_
  · exact ((hf.aestronglyMeasurable.aemeasurable.pow_const p).mul
      (hg.aestronglyMeasurable.aemeasurable.pow_const (1 - p))).aestronglyMeasurable
  · refine ae_of_all _ (fun x => ?_)
    have h0 : 0 ≤ (f x)^p * (g x)^(1-p) :=
      mul_nonneg (Real.rpow_nonneg (hf0 x) _) (Real.rpow_nonneg (hg0 x) _)
    rw [Real.norm_of_nonneg h0]
    exact rpow_mul_rpow_le_weighted_add_aux hp0 hp1 (hf0 x) (hg0 x)

theorem integral_rpow_mul_rpow_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, (f x)^p * (g x)^(1-p) ∂μ) ≤
      (∫ x, f x ∂μ)^p * (∫ x, g x ∂μ)^(1-p) := by
  have hA : 0 ≤ ∫ x, f x ∂μ := integral_nonneg (fun x => hf0 x)
  have hB : 0 ≤ ∫ x, g x ∂μ := integral_nonneg (fun x => hg0 x)
  have hRHS : 0 ≤ (∫ x, f x ∂μ)^p * (∫ x, g x ∂μ)^(1-p) :=
    mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)
  rcases hA.eq_or_lt with ha | ha
  · -- `∫ f = 0` forces `f = 0` a.e., so the integrand vanishes a.e.
    have hf_zero : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg (fun x => hf0 x) hf).1 ha.symm
    have hint : (fun x => (f x)^p * (g x)^(1-p)) =ᵐ[μ] 0 := by
      filter_upwards [hf_zero] with x hx
      simp [hx, Real.zero_rpow hp0.ne']
    have h0 : ∫ x, (f x)^p * (g x)^(1-p) ∂μ = 0 := by
      rw [integral_congr_ae hint]
      simp
    rw [h0]
    exact hRHS
  rcases hB.eq_or_lt with hb | hb
  · -- `∫ g = 0` forces `g = 0` a.e., so the integrand vanishes a.e.
    have hg_zero : g =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg (fun x => hg0 x) hg).1 hb.symm
    have hint : (fun x => (f x)^p * (g x)^(1-p)) =ᵐ[μ] 0 := by
      filter_upwards [hg_zero] with x hx
      simp [hx, Real.zero_rpow (sub_pos.mpr hp1).ne']
    have h0 : ∫ x, (f x)^p * (g x)^(1-p) ∂μ = 0 := by
      rw [integral_congr_ae hint]
      simp
    rw [h0]
    exact hRHS
  set a := ∫ x, f x ∂μ with ha_def
  set b := ∫ x, g x ∂μ with hb_def
  have hap : 0 < a ^ p := Real.rpow_pos_of_pos ha p
  have hbp : 0 < b ^ (1 - p) := Real.rpow_pos_of_pos hb _
  have hfa : Integrable (fun x => f x / a) μ := hf.div_const a
  have hgb : Integrable (fun x => g x / b) μ := hg.div_const b
  have hu : Integrable (fun x => (f x / a)^p * (g x / b)^(1 - p)) μ :=
    integrable_rpow_mul_rpow_of_integrable μ hp0 hp1
      (fun x => div_nonneg (hf0 x) ha.le) (fun x => div_nonneg (hg0 x) hb.le) hfa hgb
  have hlin : Integrable (fun x => p * (f x / a) + (1 - p) * (g x / b)) μ :=
    (hfa.const_mul p).add (hgb.const_mul (1 - p))
  have hbound : ∫ x, (f x / a)^p * (g x / b)^(1 - p) ∂μ ≤ 1 := by
    have hw : ∫ x, (p * (f x / a) + (1 - p) * (g x / b)) ∂μ = 1 := by
      rw [integral_add (hfa.const_mul p) (hgb.const_mul (1 - p)), integral_const_mul,
        integral_const_mul, integral_div, integral_div, ← ha_def, ← hb_def,
        div_self ha.ne', div_self hb.ne']
      ring
    -- compose with `hw` instead of rewriting `1` (which would also hit the exponent `1 - p`)
    refine (integral_mono hu hlin (fun x => ?_)).trans hw.le
    exact rpow_mul_rpow_le_weighted_add_aux hp0 hp1
      (div_nonneg (hf0 x) ha.le) (div_nonneg (hg0 x) hb.le)
  have hid : (fun x => (f x)^p * (g x)^(1-p))
      = fun x => (a ^ p * b ^ (1 - p)) * ((f x / a)^p * (g x / b)^(1 - p)) := by
    funext x
    rw [Real.div_rpow (hf0 x) ha.le, Real.div_rpow (hg0 x) hb.le]
    have hap' : a ^ p ≠ 0 := hap.ne'
    have hbp' : b ^ (1 - p) ≠ 0 := hbp.ne'
    field_simp
  rw [hid, integral_const_mul]
  exact mul_le_of_le_one_right (mul_pos hap hbp).le hbound

end EinsteinRelation.Correctors
