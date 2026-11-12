import EinsteinRelation.Correctors.AKMHeatKernelConsequences
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! # Bounds for the actual AKM kernel

Source: `paper/main.tex:787–792,850`; AKM Proposition E.1, (E.4),
(E.7). These bounds retain the specified kernel and its pointwise values.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The Gaussian estimate gives a spatially uniform bound on every strip
bounded away from time zero. Source: `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_uniform_bound {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a ≤ t → ∀ x y : Vec d, |P t x y| ≤ B := by
  let α : ℝ := K⁻¹ / 2
  have hα : 0 < α := half_pos (inv_pos.mpr hK)
  have hαK : α < K⁻¹ := half_lt_self (inv_pos.mpr hK)
  have hb := h.2.2.2.2.2.2.2.1 α hα hαK
  have hC : 0 ≤ C α := by
    have hh := (hb 1 zero_lt_one 0 0).1
    simp only [Real.one_rpow, mul_one, sub_self, euclideanSq, dot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_div, Real.exp_zero] at hh
    exact (abs_nonneg _).trans hh
  refine ⟨C α * a ^ (-(d : ℝ) / 2), mul_nonneg hC (Real.rpow_nonneg ha.le _), ?_⟩
  intro t ht x y
  have ht0 : 0 < t := ha.trans_le ht
  have hsq : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg ((x-y) j)
  have hexp : Real.exp (-α * euclideanSq (x-y) / (4*t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) hsq) (by positivity)
  calc
    |P t x y| ≤ C α * t ^ (-(d : ℝ) / 2) *
        Real.exp (-α * euclideanSq (x-y) / (4*t)) := (hb t ht0 x y).1
    _ ≤ C α * t ^ (-(d : ℝ) / 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
        (mul_nonneg hC (Real.rpow_nonneg ht0.le _))
    _ ≤ C α * a ^ (-(d : ℝ) / 2) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ha ht
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d))
            (by norm_num))) hC

/-- A positive-time kernel slice is globally square-integrable, using
mass one and its spatial bound. Source: `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_slice_memLp {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C) {t : ℝ} (ht : 0 < t) (y : Vec d) :
    MemLp (fun x => P t x y) 2 volume := by
  obtain ⟨B, hB, hb⟩ := akm_heatKernel_uniform_bound hK h ht
  have hi := (h.2.2.2.2.2.1 t ht y).2.2.1
  have hm := hi.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hi.const_mul B).mono' (hm.pow 2)
  filter_upwards with x
  have hx := hb t le_rfl x y
  have hp := h.2.1 t ht x y
  change ‖P t x y ^ 2‖ ≤ B * P t x y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two, mul_comm B]
  exact mul_le_mul_of_nonneg_left ((le_abs_self (P t x y)).trans hx) hp

/-- Mass one also controls the scalar energy on a whole-space strip.
Source: `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_strip_memLp {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C)
    {a b : ℝ} (ha : 0 < a) (y : Vec d) :
    MemLp (fun z : ℝ × Vec d => P z.1 z.2 y) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioo a b)
  let μ : Measure (ℝ × Vec d) := ν.prod volume
  have hμ : μ = volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d))) := by
    change (volume.restrict (Set.Ioo a b)).prod volume =
      ((volume : Measure ℝ).prod volume).restrict (Set.Ioo a b ×ˢ Set.univ)
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hc : ContinuousOn (fun z : ℝ × Vec d => P z.1 z.2 y)
      (Set.Ioo a b ×ˢ Set.univ) := by
    exact h.1.comp
      ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
      (fun z hz => ⟨ha.trans hz.1.1, Set.mem_univ _⟩)
  have hm : AEStronglyMeasurable (fun z : ℝ × Vec d => P z.1 z.2 y) μ := by
    rw [hμ]
    exact hc.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  have ht : ∀ᵐ t ∂ν, 0 < t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ha.trans ht.1
  have hi : Integrable (fun z : ℝ × Vec d => P z.1 z.2 y) μ := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · filter_upwards [ht] with t ht
      exact (h.2.2.2.2.2.1 t ht y).2.2.1
    · haveI : IsFiniteMeasure ν := by dsimp only [ν]; infer_instance
      apply (integrable_const (1 : ℝ)).congr
      filter_upwards [ht] with t ht
      have heq : (∫ x, ‖P t x y‖ ∂volume) = 1 := by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (h.2.1 t ht _ _)] using
          (h.2.2.2.2.2.1 t ht y).2.2.2
      exact heq.symm
  obtain ⟨B, _, hb⟩ := akm_heatKernel_uniform_bound hK h ha
  rw [← hμ]
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hi.const_mul B).mono' (hm.pow 2)
  have hmem : ∀ᵐ z ∂μ, z ∈ Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)) := by
    rw [hμ]
    exact ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)
  filter_upwards [hmem] with z hz
  have hp := h.2.1 z.1 (ha.trans hz.1.1) z.2 y
  change ‖P z.1 z.2 y ^ 2‖ ≤ B * P z.1 z.2 y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two, mul_comm B]
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self (P z.1 z.2 y)).trans (hb z.1 hz.1.1.le z.2 y)) hp

end EinsteinRelation.Correctors
