import EinsteinRelation.Correctors.SemigroupSpatialTranslation
import EinsteinRelation.External.AKMHeatKernel
import Mathlib.MeasureTheory.Integral.Average

/-! # Spatial translation of the actual fundamental solution

Source: `paper/main.tex:777–808`; AKM Proposition E.1, pp. 500–501.
These are changes of spatial variables in the existing weak equations.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Translation preserves the point-mass initial trace as well as the
positive-time parabolic equation. Source: `paper/main.tex:777–784`. -/
theorem fundamentalSolution_spatial_translation {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {y : Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsFundamentalSolution A y u G) (v : Vec d) :
    IsFundamentalSolution (translateCoefficient v A) (y-v)
      (fun z => u (z.1,v+z.2)) (fun z => G (z.1,v+z.2)) := by
  refine ⟨parabolicFamily_translate_space hsol.1 v, ?_⟩
  intro ψ hψ
  have hψv : IsSpatialTest Set.univ (fun x => ψ (x-v)) :=
    ⟨hψ.1.comp (contDiff_id.sub contDiff_const),
      hψ.2.1.comp_homeomorph (Homeomorph.addRight (-v)),Set.subset_univ _⟩
  have he (t : ℝ) : (∫ x, u (t,v+x)*ψ x) = ∫ x, u (t,x)*ψ (x-v) := by
    rw [← integral_add_left_eq_self (fun x => u (t,x)*ψ (x-v)) v]
    simp only [add_sub_cancel_left]
  simpa only [he] using hsol.2 _ hψv

namespace KernelTranslation

variable {E : Type*} [NormedAddCommGroup E]
  [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- A translated local integral uses the preimage of its original domain. -/
theorem locallyIntegrableOn_add_left {f : E → ℝ} {S : Set E}
    (hf : LocallyIntegrableOn f S volume) (v : E) :
    LocallyIntegrableOn (fun x => f (v+x)) ((fun x => v+x) ⁻¹' S) volume := by
  intro x hx
  obtain ⟨U,hU,hi⟩ := hf (v+x) hx
  refine ⟨(fun x => v+x) ⁻¹' U, ?_, ?_⟩
  · exact ((continuous_const.add continuous_id).continuousWithinAt.tendsto_nhdsWithin
      (fun _ hz => hz)) hU
  · exact ((measurePreserving_add_left volume v).integrableOn_comp_preimage
      (MeasurableEquiv.addLeft v).measurableEmbedding).mpr hi

/-- A translation preserves the volume-normalized integral, even when
the integrand is not integrable. -/
theorem average_add_left (v : E) (S : Set E) (f : E → ℝ) :
    (⨍ x in (fun x => v+x) ⁻¹' S, f (v+x)) = ⨍ x in S, f x := by
  have h := (measurePreserving_add_left volume v).restrict_preimage_emb
    (MeasurableEquiv.addLeft v).measurableEmbedding S
  have hm := h.measure_preimage MeasurableSet.univ
  simp only [Set.preimage_univ,Measure.restrict_apply_univ] at hm
  simp only [average_eq,measureReal_restrict_apply_univ,smul_eq_mul]
  rw [show volume.real ((fun x => v+x) ⁻¹' S) = volume.real S from congrArg ENNReal.toReal hm]
  rw [h.integral_comp (MeasurableEquiv.addLeft v).measurableEmbedding]

end KernelTranslation

/-- Translation preserves the actual mixed weak derivative of the kernel.
Source: `paper/main.tex:777–784`; AKM (E.9), p. 501. -/
theorem heatKernelMixedDerivative_spatial_translation {d : ℕ}
    {P : ℝ → Vec d → Vec d → ℝ} {H : ℝ → Vec d → Vec d → Mat d}
    (h : IsHeatKernelMixedDerivative P H) (v : Vec d) :
    IsHeatKernelMixedDerivative (fun t x y => P t (v+x) (v+y))
      (fun t x y => H t (v+x) (v+y)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (Vec d × Vec d)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × (Vec d × Vec d))) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let c : ℝ × (Vec d × Vec d) := (0,(v,v))
  have hpre : (fun z => c+z) ⁻¹' (Set.Ioi 0 ×ˢ Set.univ) =
      Set.Ioi 0 ×ˢ Set.univ := by
    ext z
    simp [c]
  refine ⟨fun i j => ?_, ?_⟩
  · simpa only [hpre,c,Prod.fst_add,Prod.snd_add,zero_add] using
      KernelTranslation.locallyIntegrableOn_add_left (h.1 i j) c
  · intro ψ hψ hψc hψs i j
    let φ : ℝ × (Vec d × Vec d) → ℝ := fun z => ψ (-c+z)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_const.add contDiff_id)
    have hφc : HasCompactSupport φ :=
      hψc.comp_homeomorph (Homeomorph.addLeft (-c))
    have hs : tsupport φ ⊆ (fun z => -c+z) ⁻¹' tsupport ψ := by
      apply closure_minimal ?_ ((isClosed_tsupport ψ).preimage (continuous_const.add continuous_id))
      intro z hz
      exact subset_tsupport ψ hz
    have hφs : tsupport φ ⊆ Set.Ioi 0 ×ˢ Set.univ := by
      intro z hz
      simpa only [c,Set.mem_preimage,Set.mem_prod,Prod.fst_add,Prod.fst_neg,
        neg_zero,zero_add] using hψs (hs hz)
    have hd (z a b : ℝ × (Vec d × Vec d)) :
        fderiv ℝ (fun w => fderiv ℝ φ w a) (c+z) b =
          fderiv ℝ (fun w => fderiv ℝ ψ w a) z b := by
      simp only [φ,fderiv_comp_add_left]
      simpa only [neg_add_cancel_left] using congrArg (fun D => D b)
        (fderiv_comp_add_left (𝕜 := ℝ) (f := fun w => fderiv ℝ ψ w a) (x := c+z) (-c))
    have he := h.2 φ hφ hφc hφs i j
    rw [← integral_add_left_eq_self
      (fun z => P z.1 z.2.1 z.2.2 *
        fderiv ℝ (fun w => fderiv ℝ φ w (0,(0,unitVector j))) z (0,(unitVector i,0))) c,
      ← integral_add_left_eq_self (fun z => H z.1 z.2.1 z.2.2 i j * φ z) c] at he
    simpa only [hd,φ,neg_add_cancel_left,c,Prod.fst_add,Prod.snd_add,zero_add] using he

/-- A simultaneous translation of the observable and its Lebesgue point
preserves the exact normalized ball condition in E.1. -/
theorem heatKernelLebesguePoint_spatial_translation {d : ℕ}
    {f : Vec d → ℝ} {y : Vec d} (h : IsHeatKernelLebesguePoint f y) (v : Vec d) :
    IsHeatKernelLebesguePoint (fun x => f (v+x)) (y-v) := by
  have he (r : ℝ) :
      (⨍ z in Metric.closedBall (WithLp.toLp 2 (y-v) : EuclideanSpace ℝ (Fin d)) r,
        |f (v+WithLp.ofLp z)-f (v+(y-v))|) =
      ⨍ z in Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
        |f (WithLp.ofLp z)-f y| := by
    have hp : (fun z : EuclideanSpace ℝ (Fin d) => WithLp.toLp 2 v+z) ⁻¹'
        Metric.closedBall (WithLp.toLp 2 y) r = Metric.closedBall (WithLp.toLp 2 (y-v)) r := by
      ext z
      simp only [Set.mem_preimage,Metric.mem_closedBall,dist_eq_norm,WithLp.toLp_sub]
      have hz : WithLp.toLp 2 v+z-WithLp.toLp 2 y =
          z-(WithLp.toLp 2 y-WithLp.toLp 2 v) := by abel
      rw [hz]
    have ha := KernelTranslation.average_add_left
      (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))
      (Metric.closedBall (WithLp.toLp 2 y) r) (fun z => |f (WithLp.ofLp z)-f y|)
    simpa only [hp,WithLp.ofLp_add,WithLp.ofLp_toLp,add_sub_cancel] using ha
  simpa only [IsHeatKernelLebesguePoint,he] using h

/-- The full E.1 contract is preserved by simultaneous spatial translation
of the coefficient and the kernel variables. Source: `paper/main.tex:777–808`;
AKM Proposition E.1, pp. 500–501. -/
theorem heatKernelProperties_spatial_translation {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C) (v : Vec d) :
    HeatKernelProperties (translateCoefficient v A)
      (fun t x y => P t (v+x) (v+y))
      (fun t x y => X t (v+x) (v+y))
      (fun t x y => Y t (v+x) (v+y))
      (fun t x y => H t (v+x) (v+y)) C := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × Vec d)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  letI : Measure.IsAddHaarMeasure (volume : Measure (Vec d × Vec d)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × (Vec d × Vec d))) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  rcases hP with ⟨hc,hpos,hX,hY,hsym,hmass,hmixed,hbound,htrace⟩
  have hdiff (x y : Vec d) : v+x-(v+y) = x-y := by abel
  have hrms (I : Set ℝ) (x : Vec d) (r : ℝ) (F : ℝ × Vec d → Vec d) :
      vectorRms volume (I ×ˢ heatKernelBall x r) (fun z => F (z.1,v+z.2)) =
      vectorRms volume (I ×ˢ heatKernelBall (v+x) r) F := by
    have hp : (fun z : ℝ × Vec d => (0,v)+z) ⁻¹' (I ×ˢ heatKernelBall (v+x) r) =
        I ×ˢ heatKernelBall x r := by
      ext z
      simp only [Set.mem_preimage,Set.mem_prod,Prod.fst_add,Prod.snd_add,zero_add,
        heatKernelBall,Set.mem_setOf_eq,hdiff]
    have hz (z : ℝ × Vec d) : ((0 : ℝ),v)+z = (z.1,v+z.2) := by
      ext <;> simp
    have ha := KernelTranslation.average_add_left ((0 : ℝ),v)
      (I ×ˢ heatKernelBall (v+x) r) (fun z => euclideanSq (F z))
    rw [hp] at ha
    simpa only [vectorRms,hz] using congrArg Real.sqrt ha
  refine ⟨?_,fun t ht x y => hpos t ht (v+x) (v+y),?_,?_,
    fun t ht x y => hsym t ht (v+x) (v+y),?_,
    heatKernelMixedDerivative_spatial_translation hmixed v,?_,?_⟩
  · exact hc.comp
      (continuous_fst.prodMk
        ((continuous_const.add continuous_snd.fst).prodMk
          (continuous_const.add continuous_snd.snd))).continuousOn
      (fun _ hz => ⟨hz.1,Set.mem_univ _⟩)
  · intro y
    simpa only [add_sub_cancel_left] using
      fundamentalSolution_spatial_translation (hX (v+y)) v
  · intro x
    simpa only [add_sub_cancel_left] using
      fundamentalSolution_spatial_translation (hY (v+x)) v
  · intro t ht x
    obtain ⟨hi,hm,hi',hm'⟩ := hmass t ht (v+x)
    exact ⟨(measurePreserving_add_left volume v).integrable_comp_of_integrable hi,
      (integral_add_left_eq_self _ v).trans hm,
      (measurePreserving_add_left volume v).integrable_comp_of_integrable hi',
      (integral_add_left_eq_self _ v).trans hm'⟩
  · intro α hα hαK t ht x y
    obtain ⟨hp,hg,hH⟩ := hbound α hα hαK t ht (v+x) (v+y)
    rw [hdiff] at hp hg hH
    refine ⟨hp,?_,?_⟩
    · intro r hr hrt
      rw [hrms _ x r (fun z => X z.1 z.2 (v+y)),
        hrms _ y r (fun z => Y z.1 (v+x) z.2)]
      exact hg r hr hrt
    · intro r hr hrt
      obtain ⟨hi,he⟩ := hH r hr hrt
      let S := Set.Ioo (t-r^2) t ×ˢ (heatKernelBall (v+x) r ×ˢ heatKernelBall (v+y) r)
      have hs : (fun z : ℝ × (Vec d × Vec d) => (0,(v,v))+z) ⁻¹' S =
          Set.Ioo (t-r^2) t ×ˢ (heatKernelBall x r ×ˢ heatKernelBall y r) := by
        ext z
        simp only [S,Set.mem_preimage,Set.mem_prod,Prod.fst_add,Prod.snd_add,
          zero_add,heatKernelBall,Set.mem_setOf_eq,hdiff]
      have hz (z : ℝ × (Vec d × Vec d)) : ((0 : ℝ),(v,v))+z =
          (z.1,(v+z.2.1,v+z.2.2)) := by
        ext <;> simp
      have hm := (measurePreserving_add_left volume ((0 : ℝ),(v,v))).integrableOn_comp_preimage
        (MeasurableEquiv.addLeft ((0 : ℝ),(v,v))).measurableEmbedding
        (f := fun z : ℝ × (Vec d × Vec d) =>
          ∑ i : Fin d, ∑ j : Fin d, (H z.1 z.2.1 z.2.2 i j)^2) (s := S)
      refine ⟨?_,?_⟩
      · have hi' := hm.mpr hi
        rw [hs] at hi'
        simpa only [hz,Function.comp_def] using hi'
      · have ha := KernelTranslation.average_add_left ((0 : ℝ),(v,v)) S
          (fun z => ∑ i : Fin d, ∑ j : Fin d, (H z.1 z.2.1 z.2.2 i j)^2)
        rw [hs] at ha
        simp only [hz] at ha
        rw [ha]
        exact he
  · intro f hf y hgrowth hlebesgue
    let f₀ : Vec d → ℝ := fun x => f (x-v)
    have hf₀ : LocallyIntegrable f₀ volume := by
      have h := KernelTranslation.locallyIntegrableOn_add_left
        (hf.locallyIntegrableOn Set.univ) (-v)
      rw [Set.preimage_univ,locallyIntegrableOn_univ] at h
      simpa only [sub_eq_add_neg,add_comm,f₀] using h
    have hgrowth₀ : ∃ k : ℝ, 0 ≤ k ∧ Integrable
        (fun x => |f₀ x| * Real.exp (-k*euclideanSq (x-(v+y)))) volume := by
      obtain ⟨k,hk,hi⟩ := hgrowth
      refine ⟨k,hk,?_⟩
      apply ((measurePreserving_add_left volume v).integrable_comp_emb
        (MeasurableEquiv.addLeft v).measurableEmbedding).mp
      simpa only [Function.comp_def,f₀,add_sub_cancel_left,hdiff] using hi
    have hleb₀ : IsHeatKernelLebesguePoint f₀ (v+y) := by
      have h := heatKernelLebesguePoint_spatial_translation hlebesgue (-v)
      simpa only [sub_neg_eq_add,add_comm,sub_eq_add_neg,neg_neg,f₀] using h
    have he (t : ℝ) : (∫ x, P t (v+x) (v+y)*f x) =
        ∫ x, P t x (v+y)*f₀ x := by
      rw [← integral_add_left_eq_self (fun x => P t x (v+y)*f₀ x) v]
      simp only [f₀,add_sub_cancel_left]
    simpa only [he,f₀,add_sub_cancel_left] using htrace f₀ hf₀ (v+y) hgrowth₀ hleb₀

end EinsteinRelation.Correctors
