import EinsteinRelation.Calculus.CoordinateTranslationPath
import EinsteinRelation.Correctors.StationaryKernelConvolution

/-! # Measurability of literal coordinate path primitives

Source: `paper/main.tex:1021–1029`. Reparametrizing every segment by the
fixed unit interval gives jointly measurable representatives.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- Fixed-interval representation of the coordinate primitive
(`paper/main.tex:1021–1029`). -/
theorem coordinatePathFlux_eq_unit_integral {d : ℕ} (f : FieldPair d → ℝ)
    (z : Vec d) (ω : FieldPair d) (i : Fin d) :
    coordinatePathFlux f z ω i = z i *
      ∫ t in (0 : ℝ)..1, f (translate (coordinateSegment z i (t * z i)) ω) := by
  simpa only [coordinatePathFlux, zero_mul, one_mul, smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_mul_right
      (fun t => f (translate (coordinateSegment z i t) ω)) (a := (0 : ℝ)) (b := 1) (z i)).symm

/-- Joint continuity of the normalized displacement path
(`paper/main.tex:1021–1029`). -/
theorem continuous_coordinateSegment_unit {d : ℕ} (i : Fin d) :
    Continuous (fun q : Vec d × ℝ => coordinateSegment q.1 i (q.2 * q.1 i)) := by
  unfold coordinateSegment coordinatePrefix
  apply Continuous.add
  · apply continuous_pi
    intro j
    by_cases h : j.val < i.val
    · simpa only [if_pos h] using (continuous_apply j).comp continuous_fst
    · simp only [if_neg h]
      exact continuous_const
  · exact (continuous_snd.mul ((continuous_apply i).comp continuous_fst)).smul continuous_const

/-- A measurable stationary field has jointly measurable coordinate path
primitives (`paper/main.tex:1021–1029`). -/
theorem measurable_coordinatePathFlux {d : ℕ} {f : FieldPair d → ℝ}
    (hf : Measurable f) : Measurable (fun q : Vec d × FieldPair d => coordinatePathFlux f q.1 q.2) := by
  apply measurable_pi_lambda
  intro i
  have hT : Measurable (fun q : (Vec d × FieldPair d) × ℝ =>
      translate (coordinateSegment q.1.1 i (q.2 * q.1.1 i)) q.1.2) :=
    Probability.continuous_translate.measurable.comp
      (((continuous_coordinateSegment_unit i).measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
          (measurable_snd.comp measurable_fst))
  have hF : StronglyMeasurable (fun q : (Vec d × FieldPair d) × ℝ =>
      f (translate (coordinateSegment q.1.1 i (q.2 * q.1.1 i)) q.1.2)) := (hf.comp hT).stronglyMeasurable
  simp_rw [coordinatePathFlux_eq_unit_integral]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    (hF.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))).measurable

end EinsteinRelation
