import EinsteinRelation.Diffusion.PhysicalSobolevTranslation
import EinsteinRelation.Diffusion.ConjugatedClosedForm
import EinsteinRelation.Probability.ConjugateSemigroup
import EinsteinRelation.Probability.ConjugateReversibility
import EinsteinRelation.Diffusion.ConjugateCylinderIntegral
import EinsteinRelation.Probability.EquivDensityTransport
import EinsteinRelation.Regeneration.SpatialRecenterEquiv
import EinsteinRelation.Environment.ActualImageLpTransportSupport

/-!
# Translating the actual fixed-environment diffusion

Source `paper/main.tex:406–408`. This construction translates the path
law, transition semigroup, heat kernel, and full weighted closed form.
It introduces no new diffusion or covariance input.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.External.GantertSection7Support

/-- Spatial conjugation preserves every field of the fixed-environment
GMP realization, including the full Sobolev domain and form limit. -/
def translateRealization {d : ℕ}
    (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) (a : Vec d) :
    GantertFixedEnvironmentRealization hd Λ hΛ (translate a ω)
      ((ActualImageLpStateTransport.isRegular_translate_iff a ω).mpr hω) lam h0 h1 := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft a
  let p := Regeneration.recenterPathEquiv a
  let L : Kernel (Vec d) (Path d) := (r.pathLaw.comap e e.measurable).map p
  let K : ℝ≥0 → Kernel (Vec d) (Vec d) := fun t => Probability.conjugateKernel e (r.transitionKernel t)
  let c := Real.exp (-2 * lam * a (firstCoordinateIndex hd))
  have hc : 0 < c := Real.exp_pos _
  have hm : (physicalReversibleMeasure (translate a ω) hd lam).map e =
      ENNReal.ofReal c • physicalReversibleMeasure ω hd lam :=
    map_add_left_physicalReversibleMeasure ω hd lam a
  haveI := r.pathLaw_isMarkovKernel
  letI : ∀ t, IsMarkovKernel (r.transitionKernel t) := r.transitionKernel_isMarkovKernel
  have hL : ∀ x, L x = (r.pathLaw (e x)).map p := by
    intro x
    rw [Kernel.map_apply _ p.measurable, Kernel.comap_apply]
  have hK := Probability.conjugate_kernel_semigroup e r.transitionKernel
    r.transitionKernel_zero r.transitionKernel_add
  refine {
    pathLaw := L
    transitionKernel := K
    heatKernel := fun t x y => r.heatKernel t (a + x) (a + y)
    pathLaw_isMarkovKernel := Kernel.IsMarkovKernel.map _ p.measurable
    transitionKernel_isMarkovKernel := fun _ => inferInstance
    transitionKernel_zero := hK.1
    transitionKernel_add := hK.2
    transitionKernel_reversible := ?_
    pathLaw_starts_at := ?_
    heatKernel_aeMeasurable := ?_
    transitionKernel_eq_heatKernel := ?_
    pathLaw_endpoint := ?_
    pathLaw_ordered_finite_dimensional := ?_
    closedForm_domain := ?_
    closedForm_value := ?_
  }
  · intro t A B hA hB
    exact Probability.conjugate_kernel_reversible e _ _ (ENNReal.ofReal c)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top hm
      (r.transitionKernel t) (r.transitionKernel_reversible t) A B hA hB
  · intro x
    rw [hL]
    apply p.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [r.pathLaw_starts_at (e x)] with γ hγ
    change pathPosition 0 γ - a = x
    rw [hγ]
    simp [e]
  · intro t ht x
    have h := r.heatKernel_aeMeasurable t ht (a + x)
    have hp := measurePreserving_add_left (volume : Measure (Vec d)) a
    exact h.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  · intro t ht x
    rw [Probability.conjugateKernel_apply, r.transitionKernel_eq_heatKernel t ht]
    simpa [e, sub_eq_add_neg, add_comm] using Probability.map_sub_const_withDensity_volume a
      (r.heatKernel t (a + x)) (r.heatKernel_aeMeasurable t ht (a + x))
  · intro t x
    rw [hL, Probability.conjugateKernel_apply,
      Measure.map_map (measurable_pathPosition t) p.measurable]
    rw [← r.pathLaw_endpoint t (e x), Measure.map_map e.symm.measurable
      (measurable_pathPosition t)]
    congr 1
    funext γ
    change γ t - a = -a + γ t
    abel
  · intro increments x F hF hb
    rw [hL, integral_map_equiv]
    change _ = iteratedMarkovCylinderIntegral
      (fun t => ((r.transitionKernel t).comap e e.measurable).map e.symm) increments F x
    rw [iteratedMarkovCylinderIntegral_conjugate]
    have he : Continuous (e.symm : Vec d → Vec d) := by
      change Continuous (fun x : Vec d => -a + x)
      fun_prop
    have hl : Continuous (fun ys : List (Vec d) => ys.map e.symm) := by
      apply continuous_iff_continuousAt.mpr
      apply List.tendsto_nhds
      · exact tendsto_pure_nhds _ _
      · intro ys y ih
        exact (Filter.Tendsto.comp (he.tendsto y) tendsto_fst).cons
          (Filter.Tendsto.comp ih tendsto_snd)
    have hFm : Measurable (fun ys : List (Vec d) => F (ys.map e.symm)) :=
      hF.comp hl.measurable
    have h := r.pathLaw_ordered_finite_dimensional increments (e x)
      (fun ys => F (ys.map e.symm)) hFm (by
        obtain ⟨B, hB⟩ := hb
        exact ⟨B, fun ys => hB _⟩)
    convert h using 1
    congr 1
    funext γ
    congr 1
    simp [pathPositionsAtTimes, pathPosition, p, Regeneration.recenterPathEquiv, e, sub_eq_add_neg, add_comm,
      List.map_map, Function.comp_def]
  · intro f hf
    exact closedForm_domain_conjugate hd Λ hΛ ω hω lam h0 h1 r (translate a ω) e c hc hm
      (physicalH1Member_translate_iff ω hd lam a) f hf
  · intro f q hq u hu
    exact closedForm_value_conjugate hd Λ hΛ ω hω lam h0 h1 r (translate a ω) e c hc hm
      (physicalH1Member_translate_iff ω hd lam a) (translatePhysicalGraph hd lam (-a))
      (by intro u x; simp [translatePhysicalGraph, e])
      (physicalH1FormEnergy_translate ω hd lam a) f q hq u hu


end EinsteinRelation.External.GantertSection7Support
