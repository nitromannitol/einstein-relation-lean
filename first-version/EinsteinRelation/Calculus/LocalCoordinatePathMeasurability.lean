import EinsteinRelation.Calculus.CoordinatePathMeasurability
import EinsteinRelation.Calculus.CoordinatePathGeometry
import EinsteinRelation.Environment.LocalIntegralMeasurability
import Mathlib.Topology.Order.ProjIcc

open MeasureTheory

noncomputable section
namespace EinsteinRelation

/-- The literal coordinate path observes only the displacement ball
(`paper/main.tex:1021–1029,1079–1084`). -/
theorem measurable_localSigma_coordinatePathFlux_ball {d : ℕ}
    {L : ℝ} {U W : Set (Vec d)}
    (hwindow : ∀ x : Vec d, euclideanNorm x < L → ∀ y ∈ U, x + y ∈ W)
    {f : FieldPair d → ℝ} (hf : Measurable[localSigma U] f) :
    @Measurable (↥{z : Vec d | euclideanNorm z < L} × FieldPair d) (Vec d)
      (@Prod.instMeasurableSpace _ _ inferInstance (localSigma W)) inferInstance
      (fun q => coordinatePathFlux f q.1 q.2) := by
  let S := {z : Vec d | euclideanNorm z < L}
  letI : MeasurableSpace (FieldPair d) := localSigma W
  apply measurable_pi_lambda
  intro i
  let c : ℝ → ℝ := fun t => (Set.projIcc (0 : ℝ) 1 (by norm_num) t : ℝ)
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcmem t : c t ∈ Set.Icc (0 : ℝ) 1 := (Set.projIcc (0 : ℝ) 1 (by norm_num) t).property
  let g : (↥S × FieldPair d) × ℝ → Vec d :=
    fun q => coordinateSegment q.1.1 i (c q.2 * q.1.1.1 i)
  have hg : Measurable g := (continuous_coordinateSegment_unit i).measurable.comp
    ((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
      (hc.measurable.comp measurable_snd))
  have hgS q : g q ∈ S := by
    apply lt_of_le_of_lt (euclideanNorm_coordinateSegment_bound q.1.1.1 i ?_) q.1.1.2
    have ht := hcmem q.2
    rcases le_total 0 (q.1.1.1 i) with hz | hz
    · rw [Set.uIcc_of_le hz]
      constructor <;> nlinarith [ht.1, ht.2]
    · rw [Set.uIcc_of_ge hz]
      constructor <;> nlinarith [ht.1, ht.2]
  have hT : @Measurable ((↥S × FieldPair d) × ℝ) (FieldPair d)
      inferInstance (localSigma U)
      (fun q => translate (g q) q.1.2) :=
    (measurable_translate_joint (S := S) hwindow).comp
      ((hg.subtype_mk (h := hgS)).prodMk (measurable_snd.comp measurable_fst))
  have hF := (hf.comp hT).stronglyMeasurable
  have hInt := (hF.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))).measurable
  have he : (fun q : ↥S × FieldPair d => coordinatePathFlux f q.1 q.2 i) =
      fun q => q.1.1 i * ∫ t in Set.Ioc (0 : ℝ) 1, f (translate (g (q,t)) q.2) := by
    funext q
    rw [coordinatePathFlux_eq_unit_integral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only [g,c]
    rw [Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ⟨ht.1.le,ht.2⟩]
  rw [he]
  exact ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst)).mul hInt

end EinsteinRelation
