import EinsteinRelation.Correctors.AKMHeatKernelPrescribedGradient

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Fundamental solutions of one scalar field have the same gradient on
any bounded positive cylinder. Source: `paper/main.tex:787–792,850`. -/
theorem fundamentalSolution_gradients_ae_on_cylinder
    {d : ℕ} {K : ℝ} {A : Coefficient d K} {y : Vec d}
    {u : ℝ × Vec d → ℝ} {G Z : ℝ × Vec d → Vec d}
    (hG : IsFundamentalSolution A y u G) (hZ : IsFundamentalSolution A y u Z)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R) :
    G =ᵐ[volume.restrict (Set.Ioo a b ×ˢ originBall d R)] Z := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo a b)
  let ν : Measure (Vec d) := volume.restrict (originBall d R)
  have hGm : AEStronglyMeasurable G (μ.prod ν) := by
    simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using
      (hG.1 a b R ha hab hR).2.1
  have hZm : AEStronglyMeasurable Z (μ.prod ν) := by
    simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using
      (hZ.1 a b R ha hab hR).2.1
  have hsub : Set.Ioo a b ⊆ Set.Ioi 0 := fun t ht => ha.trans ht.1
  have heq : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, G (t,x) = Z (t,x) := by
    filter_upwards [(akm_fundamental_energy_slices hG.1).filter_mono
        (ae_mono (Measure.restrict_mono hsub le_rfl)),
      (akm_fundamental_energy_slices hZ.1).filter_mono
        (ae_mono (Measure.restrict_mono hsub le_rfl))] with t htG htZ
    exact (htG.1.ae_eq_of_same_potential htZ.1).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hmk : hGm.mk G =ᵐ[μ.prod ν] hZm.mk Z := by
    apply (Measure.ae_prod_iff_ae_ae
      (hGm.stronglyMeasurable_mk.measurableSet_eq_fun hZm.stronglyMeasurable_mk)).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hGm.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hZm.ae_eq_mk,heq] with t htG htZ ht
    filter_upwards [htG,htZ,ht] with x hxG hxZ hx
    exact hxG.symm.trans (hx.trans hxZ)
  simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using
    hGm.ae_eq_mk.trans (hmk.trans hZm.ae_eq_mk.symm)

/-- Symmetric prescribed spatial derivatives preserve every E.1 property,
including the same Gaussian and mixed-derivative constants.
Source: AKM E.1 (E.1)–(E.11); `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_prescribed_properties
    {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y Z : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    (hZsol : ∀ y, IsFundamentalSolution A y
      (fun z => P z.1 z.2 y) (fun z => Z z.1 z.2 y)) :
    HeatKernelProperties A P Z (fun t x y => Z t y x) H C := by
  have hswap (x : Vec d) : IsFundamentalSolution A x
      (fun z => P z.1 x z.2) (fun z => Z z.1 z.2 x) :=
    fundamentalSolution_scalar_congr_positive (hZsol x)
      (fun t ht y => hP.2.2.2.2.1 t ht y x)
  refine ⟨hP.1,hP.2.1,hZsol,hswap,hP.2.2.2.2.1,hP.2.2.2.2.2.1,
    hP.2.2.2.2.2.2.1,?_,hP.2.2.2.2.2.2.2.2⟩
  intro α hα hαK t ht x y
  have hb := hP.2.2.2.2.2.2.2.1 α hα hαK t ht x y
  refine ⟨hb.1,?_,hb.2.2⟩
  intro r hr hrt
  have ha : 0 < t-r^2 := by
    have hp := pow_le_pow_left₀ hr.le hrt 2
    have hs := Real.sq_sqrt ht.le
    nlinarith
  have hab : t-r^2 < t := by nlinarith [sq_pos_of_pos hr]
  have hR (v : Vec d) : 0 < euclideanNorm v+r+1 := by
    have hn : 0 ≤ euclideanNorm v := Real.sqrt_nonneg _
    linarith
  have hsub (v : Vec d) : heatKernelBall v r ⊆
      originBall d (euclideanNorm v+r+1) := by
    intro z hz
    have hn := TimeChange.euclideanNorm_add_le (z-v) v
    have he : z-v+v = z := sub_add_cancel z v
    rw [he] at hn
    exact lt_of_le_of_lt hn (by change euclideanNorm (z-v) < r at hz; linarith)
  have hx := fundamentalSolution_gradients_ae_on_cylinder
    (hP.2.2.1 y) (hZsol y) ha hab (hR x)
  have hy := fundamentalSolution_gradients_ae_on_cylinder
    (hP.2.2.2.1 x) (hswap x) ha hab (hR y)
  have hx' := hx.filter_mono (ae_mono (Measure.restrict_mono_set volume
    (Set.prod_mono (Set.Subset.refl _) (hsub x))))
  have hy' := hy.filter_mono (ae_mono (Measure.restrict_mono_set volume
    (Set.prod_mono (Set.Subset.refl _) (hsub y))))
  have hxr : vectorRms volume (Set.Ioo (t-r^2) t ×ˢ heatKernelBall x r)
      (fun z => X z.1 z.2 y) =
      vectorRms volume (Set.Ioo (t-r^2) t ×ˢ heatKernelBall x r)
        (fun z => Z z.1 z.2 y) := by
    unfold vectorRms
    congr 1
    apply average_congr
    exact hx'.mono fun z hz => congrArg (fun v : Vec d => euclideanSq v) hz
  have hyr : vectorRms volume (Set.Ioo (t-r^2) t ×ˢ heatKernelBall y r)
      (fun z => Y z.1 x z.2) =
      vectorRms volume (Set.Ioo (t-r^2) t ×ˢ heatKernelBall y r)
        (fun z => Z z.1 z.2 x) := by
    unfold vectorRms
    congr 1
    apply average_congr
    exact hy'.mono fun z hz => congrArg (fun v : Vec d => euclideanSq v) hz
  simpa only [hxr,hyr] using hb.2.1 r hr hrt

end EinsteinRelation.Correctors
