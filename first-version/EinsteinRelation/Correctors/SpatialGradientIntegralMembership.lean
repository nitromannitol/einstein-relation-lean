import EinsteinRelation.Correctors.EuclideanTimeSpaceCauchy
import EinsteinRelation.Correctors.SpatialGradientTimeMinkowski

/-! # Spatial L² membership of literal gradient integrals

Source: `paper/main.tex:808–816,852–857`. These membership statements
allow spatial L² triangle inequalities for the finite integral and its
infinite-time remainder without relying on totalized RMS integrals.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- A space-time L² field has a spatial L² finite-time integral.
Source: `paper/main.tex:852–857`. -/
theorem memLp_time_integral_of_memLp_spacetime
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    {T : ℝ} (hT : 0 ≤ T) {g : ℝ × X → E}
    (hg : MemLp g 2 ((volume.restrict (Icc 0 T)).prod ν)) :
    MemLp (fun x => ∫ t in Icc (0 : ℝ) T, g (t,x)) 2 ν := by
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hsq : Integrable (fun z => ‖g z‖^2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq hg.norm.aestronglyMeasurable).mp hg.norm
  have hslice : ∀ᵐ x ∂ν, MemLp (fun t => g (t,x)) 2 μ := by
    filter_upwards [hg.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with x hx hs
    exact (memLp_two_iff_integrable_sq_norm hx).mpr hs
  have hbound : ∀ᵐ x ∂ν,
      ‖∫ t in Icc (0 : ℝ) T, g (t,x)‖^2 ≤ T * ∫ t in Icc (0 : ℝ) T, ‖g (t,x)‖^2 := by
    filter_upwards [hslice] with x hx
    exact norm_time_integral_sq_le_energy hT _ hx
  have hi : Integrable (fun x => ∫ t, ‖g (t,x)‖^2 ∂μ) ν := hsq.integral_prod_right
  have hm : AEStronglyMeasurable (fun x => ∫ t, g (t,x) ∂μ) ν :=
    hg.aestronglyMeasurable.prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact (hi.const_mul T).mono' (hm.norm.pow 2) (by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx)

/-- Integrable spatial RMS and almost-everywhere energy slices give a
genuine spatial L² tail. Source: `paper/main.tex:808–816`. -/
theorem spatialL2_tail_integral_memLp
    {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) [SigmaFinite ν] {T : ℝ} (hT : 0 < T)
    (f : ℝ × X → EuclideanSpace ℝ (Fin d)) (hf : Measurable f)
    (hsections : ∀ᵐ t ∂volume.restrict (Ioi T), MemLp (fun x => f (t,x)) 2 ν)
    (hmajorant : IntegrableOn (fun t => Real.sqrt (∫ x, ‖f (t,x)‖^2 ∂ν)) (Ioi T)) :
    MemLp (fun x => ∫ t in Ioi T, f (t,x)) 2 ν := by
  let μ := volume.restrict (Ioi T)
  let g : ℝ → ℝ := fun t => Real.sqrt (∫ x, ‖f (t,x)‖^2 ∂ν)
  have hgm : Measurable g :=
    ((hf.norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
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
  have hBi : Integrable (g + φ) μ := hmajorant.add hφi
  have hmass : 0 < ∫ t, (g + φ) t ∂μ := by
    change 0 < ∫ t, g t + φ t ∂μ
    rw [integral_add hmajorant hφi]
    exact add_pos_of_nonneg_of_pos (integral_nonneg fun _ => Real.sqrt_nonneg _) hφint
  have hbound : ∀ᵐ t ∂μ,
      eLpNorm (fun x => f (t,x)) 2 ν ≤ ENNReal.ofReal ((g + φ) t) := by
    filter_upwards [hsections] with t ht
    rw [eLpNorm_two_eq_ofReal_spatial_rms ν ht]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hφpos t).le)
  have hfm : StronglyMeasurable (fun z : X × ℝ => f (z.2,z.1)) :=
    (hf.comp measurable_swap).stronglyMeasurable
  have hb := eLpNorm_vector_integral_le_integral_bound_ae ν μ
    (by norm_num) (by norm_num) _ hfm (hgm.add hφm) hBi
    (fun t => add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (hφpos t)) hmass hbound
  exact ⟨hfm.integral_prod_right'.aestronglyMeasurable,
    lt_of_le_of_lt hb ENNReal.ofReal_lt_top⟩

end EinsteinRelation.Correctors
