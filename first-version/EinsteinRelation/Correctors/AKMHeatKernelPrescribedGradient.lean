import EinsteinRelation.Correctors.AKMHeatKernelMeasurableGradient
import EinsteinRelation.Correctors.SemigroupPrescribedGradientRecovery
import EinsteinRelation.Correctors.AKMHeatKernelBounds
import EinsteinRelation.Calculus.WeakGradientUniqueness

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- An E.1 kernel has a joint measurable gradient realizing its actual
spatial weak derivative at every positive time and every initial point.
Source: `paper/main.tex:787–792,798–806,850`. -/
theorem akm_heatKernel_exists_measurable_prescribed_gradient
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C) :
    ∃ Z : ℝ → Vec d → Vec d → Vec d,
      Measurable (fun z : ℝ × (Vec d × Vec d) => Z z.1 z.2.1 z.2.2) ∧
      (∀ y, IsFundamentalSolution A y
        (fun z => P z.1 z.2 y) (fun z => Z z.1 z.2 y)) ∧
      ∀ y t, 0 < t → HasWeakGradient Set.univ
        (fun x => P t x y) (fun x => Z t x y) := by
  classical
  have hcont (y : Vec d) : ContinuousOn (fun z : ℝ × Vec d => P z.1 z.2 y)
      (Set.Ioi 0 ×ˢ Set.univ) :=
    hP.1.comp ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
      (fun z hz => ⟨hz.1,Set.mem_univ _⟩)
  have hex (y : Vec d) (t : ℝ) (ht : 0 < t) :
      ∃ W : Vec d → Vec d, HasWeakGradient Set.univ (fun x => P t x y) W := by
    apply exists_global_weakGradient_of_ball_gradients
    intro r hr
    obtain ⟨χ,L,hL,hχ,hχb,hχr,hχD⟩ := exists_prescribed_spatial_ball_cutoff d r hr
    have hU := isCompact_closure_originBall d (2*r)
    have hV := isCompact_closure_originBall d r
    letI : IsFiniteMeasure (volume.restrict (originBall d (2*r))) :=
      isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
        (hU.measure_ne_top (μ := volume)) (measure_mono subset_closure))
    letI : IsFiniteMeasure (volume.restrict (originBall d r)) :=
      isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
        (hV.measure_ne_top (μ := volume)) (measure_mono subset_closure))
    have hopen (s : ℝ) : IsOpen (originBall d s) := by
      unfold originBall euclideanNorm euclideanSq dot
      exact isOpen_lt (by fun_prop) continuous_const
    obtain ⟨W,hw,_,_⟩ := parabolicSolution_prescribed_gradient_energy hK (half_pos ht)
      (by linarith : t/2 < t) (hopen (2*r))
      (show originBall d r ⊆ originBall d (2*r) from fun x hx =>
        lt_of_lt_of_le (show euclideanNorm x < r from hx)
          (show r ≤ 2*r by linarith only [hr])) (hopen r).measurableSet (hcont y)
      ((hP.2.2.1 y).1 (t/2) t (2*r) (half_pos ht) (by linarith) (by positivity))
      ((akm_heatKernel_slice_memLp hK hP ht y).mono_measure Measure.restrict_le_self)
      hχ hχb hχr hL hχD
    exact ⟨W,hw⟩
  let p : ℝ × (Vec d × Vec d) → ℝ := fun z =>
    if 0 < z.1 then P z.1 z.2.1 z.2.2 else 0
  have hpm : Measurable p := by
    convert hP.1.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
      (measurableSet_Ioi.prod MeasurableSet.univ) using 1
    funext z
    change (if 0 < z.1 then P z.1 z.2.1 z.2.2 else 0) =
      (if z ∈ Set.Ioi 0 ×ˢ Set.univ then P z.1 z.2.1 z.2.2 else 0)
    simp only [Set.mem_prod,Set.mem_Ioi,Set.mem_univ,and_true]
  let u : Vec d → ℝ × Vec d → ℝ := fun y z => p (z.1,(z.2,y))
  have hum : Measurable (fun z : Vec d × (ℝ × Vec d) => u z.1 z.2) :=
    hpm.comp (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
  obtain ⟨R,hRm,hrec⟩ := exists_measurable_prescribed_gradient_recovery u hum
  let Z : ℝ → Vec d → Vec d → Vec d := fun t x y => R y (t,x)
  have hZm : Measurable (fun z : ℝ × (Vec d × Vec d) => Z z.1 z.2.1 z.2.2) :=
    hRm.comp (measurable_snd.snd.prodMk (measurable_fst.prodMk measurable_snd.fst))
  have hZw (y : Vec d) (t : ℝ) (ht : 0 < t) :
      HasWeakGradient Set.univ (fun x => P t x y) (fun x => Z t x y) := by
    obtain ⟨W,hW⟩ := hex y t ht
    have huW : HasWeakGradient Set.univ (fun x => u y (t,x)) W := by
      convert hW using 1
      funext x
      simp only [u,p,if_pos ht]
    have heq := hrec y t W huW
    apply hasWeakGradient_congr_ae isOpen_univ hW Filter.EventuallyEq.rfl
    simpa only [Measure.restrict_univ] using heq.symm
  refine ⟨Z,hZm,?_,hZw⟩
  intro y
  refine ⟨?_,(hP.2.2.1 y).2⟩
  intro a b r ha hab hr
  let μ : Measure ℝ := volume.restrict (Set.Ioo a b)
  let ν : Measure (Vec d) := volume.restrict (originBall d r)
  have hsol := (hP.2.2.1 y).1 a b r ha hab hr
  have hXm : AEStronglyMeasurable (fun z : ℝ × Vec d => X z.1 z.2 y) (μ.prod ν) := by
    simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using hsol.2.1
  have hZm' : AEStronglyMeasurable (fun z : ℝ × Vec d => Z z.1 z.2 y) (μ.prod ν) :=
    (hZm.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))).aestronglyMeasurable
  have heq : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, X t x y = Z t x y := by
    have hsub : Set.Ioo a b ⊆ Set.Ioi 0 := fun t ht => ha.trans ht.1
    filter_upwards [(akm_fundamental_energy_slices (hP.2.2.1 y).1).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl)),ae_restrict_mem measurableSet_Ioo]
      with t ht htI
    exact (ht.1.ae_eq_of_same_potential (hZw y t (ha.trans htI.1))).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hmk : hXm.mk (fun z => X z.1 z.2 y) =ᵐ[μ.prod ν]
      hZm'.mk (fun z => Z z.1 z.2 y) := by
    apply (Measure.ae_prod_iff_ae_ae
      (hXm.stronglyMeasurable_mk.measurableSet_eq_fun hZm'.stronglyMeasurable_mk)).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hXm.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hZm'.ae_eq_mk,heq] with t htX htZ ht
    filter_upwards [htX,htZ,ht] with x hxX hxZ hx
    exact hxX.symm.trans (hx.trans hxZ)
  have hopen : IsOpen (originBall d r) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  apply parabolicSolution_gradient_congr_ae hopen hsol
  simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using
    hXm.ae_eq_mk.trans (hmk.trans hZm'.ae_eq_mk.symm)

end EinsteinRelation.Correctors
