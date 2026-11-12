import EinsteinRelation.Correctors.VectorTimeMinkowski
import EinsteinRelation.Correctors.FlowTimeTail
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Spatial L² Minkowski on a positive time tail

Source: `paper/main.tex:800–808`. This estimate applies directly to
local spatial gradient RMS bounds, allowing exceptional time slices.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- The spatial RMS is the real representation of the `L²` seminorm.
Source: `paper/main.tex:800–808`. -/
theorem eLpNorm_two_eq_ofReal_spatial_rms
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (ν : Measure X) {f : X → E} (hf : MemLp f 2 ν) :
    eLpNorm f 2 ν = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖^2 ∂ν)) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,← one_div,← Real.sqrt_eq_rpow]
    using hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)

/-- Integrating a gradient tail in time commutes with the spatial RMS
inequality, even when spatial `L²` membership holds only almost every
time. Source: `paper/main.tex:800–808`. -/
theorem spatialL2_tail_integral_le_integral_spatialL2
    {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) [SigmaFinite ν] {T : ℝ} (hT : 0 < T)
    (f : ℝ × X → EuclideanSpace ℝ (Fin d)) (hf : Measurable f)
    (hsections : ∀ᵐ t ∂volume.restrict (Ioi T), MemLp (fun x => f (t,x)) 2 ν)
    (hmajorant : IntegrableOn (fun t => Real.sqrt (∫ x, ‖f (t,x)‖^2 ∂ν)) (Ioi T)) :
    Real.sqrt (∫ x, ‖∫ t in Ioi T, f (t,x)‖^2 ∂ν) ≤
      ∫ t in Ioi T, Real.sqrt (∫ x, ‖f (t,x)‖^2 ∂ν) := by
  let μ : Measure ℝ := volume.restrict (Ioi T)
  let g : ℝ → ℝ := fun t => Real.sqrt (∫ x, ‖f (t,x)‖^2 ∂ν)
  have hgm : Measurable g :=
    ((hf.norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have hg0 (t : ℝ) : 0 ≤ g t := Real.sqrt_nonneg _
  let φ : ℝ → ℝ := fun t => (max t T)^(-1-(1 : ℝ))
  have hφm : Measurable φ := (measurable_id.max measurable_const).pow_const _
  have hφpos (t : ℝ) : 0 < φ t :=
    Real.rpow_pos_of_pos (hT.trans_le (le_max_right _ _)) _
  have hφeq : φ =ᵐ[μ] fun t => t^(-1-(1 : ℝ)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have ht' : T < t := ht
    simp only [φ,max_eq_left ht'.le]
  have hφi : Integrable φ μ := by
    have hi : Integrable (fun t : ℝ => t^(-1-(1 : ℝ))) μ := by
      simpa only [one_mul] using
        flow_tail_integrableOn (C := 1) (by norm_num : (0 : ℝ) < 1) hT
    exact hi.congr hφeq.symm
  have hφint : 0 < ∫ t, φ t ∂μ := by
    rw [integral_congr_ae hφeq]
    have heq := flow_tail_integral_eq (C := 1) (by norm_num : (0 : ℝ) < 1) hT
    simp only [one_mul,div_one] at heq
    rw [heq]
    exact Real.rpow_pos_of_pos hT _
  have hfm : StronglyMeasurable (fun z : X × ℝ => f (z.2,z.1)) :=
    (hf.comp measurable_swap).stronglyMeasurable
  have hF : StronglyMeasurable (fun x => ∫ t, f (t,x) ∂μ) := hfm.integral_prod_right'
  have hε (ε : ℝ) (hε : 0 < ε) :
      eLpNorm (fun x => ∫ t, f (t,x) ∂μ) 2 ν ≤
        ENNReal.ofReal ((∫ t, g t ∂μ) + ε*(∫ t, φ t ∂μ)) := by
    let B := fun t => g t + ε*φ t
    have hBi : Integrable B μ := hmajorant.add (hφi.const_mul ε)
    have hBint : (∫ t, B t ∂μ) = (∫ t, g t ∂μ) + ε*(∫ t, φ t ∂μ) := by
      rw [integral_add hmajorant (hφi.const_mul ε),integral_const_mul]
    have hbound : ∀ᵐ t ∂μ, eLpNorm (fun x => f (t,x)) 2 ν ≤ ENNReal.ofReal (B t) := by
      filter_upwards [hsections] with t ht
      rw [eLpNorm_two_eq_ofReal_spatial_rms ν ht]
      exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (mul_nonneg hε.le (hφpos t).le))
    have h := eLpNorm_vector_integral_le_integral_bound_ae ν μ (by norm_num) (by norm_num)
      _ hfm (hgm.add (measurable_const.mul hφm)) hBi
      (fun t => add_pos_of_nonneg_of_pos (hg0 t) (mul_pos hε (hφpos t)))
      (by rw [hBint]; exact add_pos_of_nonneg_of_pos (integral_nonneg hg0) (mul_pos hε hφint))
      hbound
    change eLpNorm (fun x => ∫ t, f (t,x) ∂μ) 2 ν ≤ ENNReal.ofReal (∫ t, B t ∂μ) at h
    simpa only [hBint] using h
  have hmem : MemLp (fun x => ∫ t, f (t,x) ∂μ) 2 ν :=
    ⟨hF.aestronglyMeasurable,lt_of_le_of_lt (hε 1 zero_lt_one) ENNReal.ofReal_lt_top⟩
  have hreal (ε : ℝ) (hεpos : 0 < ε) :
      Real.sqrt (∫ x, ‖∫ t, f (t,x) ∂μ‖^2 ∂ν) ≤
        (∫ t, g t ∂μ) + ε*(∫ t, φ t ∂μ) := by
    have h := hε ε hεpos
    rw [eLpNorm_two_eq_ofReal_spatial_rms ν hmem] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  apply le_of_forall_pos_le_add
  intro ε hεpos
  have h := hreal (ε/(∫ t, φ t ∂μ)) (div_pos hεpos hφint)
  simpa only [div_mul_cancel₀ ε hφint.ne'] using h

end EinsteinRelation.Correctors
