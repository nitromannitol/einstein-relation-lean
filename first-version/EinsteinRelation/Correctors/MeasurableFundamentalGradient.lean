import EinsteinRelation.External.AKMHeatKernel
import EinsteinRelation.Correctors.AKMHeatKernelEnergySlices
import EinsteinRelation.Correctors.MeasurableWeakGradient
import EinsteinRelation.Correctors.ParabolicGradientRepresentative

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Joint gradient recovery for a family of actual fundamental solutions.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1, (E.1). -/
theorem exists_measurable_fundamentalFamily_gradient
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {K : ℝ}
    (A : Ω → Coefficient d K) (y : Ω → Vec d)
    (u : Ω → ℝ × Vec d → ℝ) (G : Ω → ℝ × Vec d → Vec d)
    (hum : Measurable (fun z : Ω × (ℝ × Vec d) => u z.1 z.2))
    (hsol : ∀ ω, IsFundamentalSolution (A ω) (y ω) (u ω) (G ω)) :
    ∃ H : Ω → ℝ × Vec d → Vec d,
      Measurable (fun z : Ω × (ℝ × Vec d) => H z.1 z.2) ∧
      (∀ ω, IsFundamentalSolution (A ω) (y ω) (u ω) (H ω)) ∧
      ∀ ω, ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
        ((fun x => H ω (t,x)) =ᵐ[volume] (fun x => G ω (t,x))) ∧
        HasWeakGradient Set.univ (fun x => u ω (t,x)) (fun x => H ω (t,x)) := by
  let f : (Ω × ℝ) → Vec d → ℝ := fun z x => u z.1 (z.2,x)
  have hfm : Measurable (fun z : (Ω × ℝ) × Vec d => f z.1 z.2) :=
    hum.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  obtain ⟨H₀,hH₀m,hH₀G⟩ := exists_measurable_spatialGradient_recovery f hfm
  let H : Ω → ℝ × Vec d → Vec d := fun ω z => H₀ (ω,z.1) z.2
  have hHm : Measurable (fun z : Ω × (ℝ × Vec d) => H z.1 z.2) :=
    hH₀m.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  have hHG : ∀ ω, ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
      ((fun x => H ω (t,x)) =ᵐ[volume] (fun x => G ω (t,x))) ∧
      HasWeakGradient Set.univ (fun x => u ω (t,x)) (fun x => H ω (t,x)) := by
    intro ω
    filter_upwards [akm_fundamental_energy_slices (hsol ω).1] with t ht
    have heq : (fun x => H ω (t,x)) =ᵐ[volume] (fun x => G ω (t,x)) :=
      hH₀G (ω,t) (fun x => G ω (t,x)) ht.1
    refine ⟨heq,?_⟩
    apply hasWeakGradient_congr_ae isOpen_univ ht.1 Filter.EventuallyEq.rfl
    simpa only [Measure.restrict_univ] using heq.symm
  refine ⟨H,hHm,?_,hHG⟩
  intro ω
  refine ⟨?_,(hsol ω).2⟩
  intro a b R ha hab hR
  let μ : Measure ℝ := volume.restrict (Set.Ioo a b)
  let ν : Measure (Vec d) := volume.restrict (originBall d R)
  have hGm : AEStronglyMeasurable (G ω) (μ.prod ν) := by
    simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using
      ((hsol ω).1 a b R ha hab hR).2.1
  have hHmω : AEStronglyMeasurable (H ω) (μ.prod ν) :=
    (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have heq : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, G ω (t,x) = H ω (t,x) := by
    have hsub : Set.Ioo a b ⊆ Set.Ioi 0 := fun t ht => ha.trans ht.1
    filter_upwards [(hHG ω).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))]
      with t ht
    exact ht.1.symm.filter_mono (ae_mono Measure.restrict_le_self)
  have hmk : hGm.mk (G ω) =ᵐ[μ.prod ν] hHmω.mk (H ω) := by
    apply (Measure.ae_prod_iff_ae_ae
      (hGm.stronglyMeasurable_mk.measurableSet_eq_fun hHmω.stronglyMeasurable_mk)).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hGm.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hHmω.ae_eq_mk,heq] with t htG htH ht
    filter_upwards [htG,htH,ht] with x hxG hxH hx
    exact hxG.symm.trans (hx.trans hxH)
  have hball : IsOpen (originBall d R) := by
    apply isOpen_lt _ continuous_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  apply parabolicSolution_gradient_congr_ae hball ((hsol ω).1 a b R ha hab hR)
  simpa only [μ,ν,Measure.prod_restrict,← Measure.volume_eq_prod] using
    hGm.ae_eq_mk.trans (hmk.trans hHmω.ae_eq_mk.symm)

end EinsteinRelation.Correctors
