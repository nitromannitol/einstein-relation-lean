import EinsteinRelation.Correctors.SemigroupPrescribedGradient
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- An integrable envelope for translated local norm integrals implies
whole-space absolute convergence. Source: AKM (9.9), p. 350;
`paper/main.tex:787–792,850`. -/
theorem integrable_of_translated_local_norm_envelope {d : ℕ}
    {F : Vec d → Vec d} (hF : Measurable F)
    {B : Set (Vec d)} (hBpos : volume B ≠ 0)
    {w : Vec d → ℝ} (hw : Integrable w volume)
    (hlocal : ∀ a : Vec d, IntegrableOn (fun x => ‖F (a+x)‖) B volume)
    (hbound : ∀ a : Vec d, (∫ x in B, ‖F (a+x)‖) ≤ w a) :
    Integrable F volume := by
  let ν : Measure (Vec d) := volume.restrict B
  letI : NeZero ν := ⟨Measure.restrict_eq_zero.not.mpr hBpos⟩
  have hm : Measurable (fun z : Vec d × Vec d => F (z.1+z.2)) :=
    hF.comp (measurable_fst.add measurable_snd)
  have havg : Integrable (fun a : Vec d => ∫ x, ‖F (a+x)‖ ∂ν) volume := by
    apply hw.mono' hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards with a
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    exact hbound a
  have hi : Integrable (fun z : Vec d × Vec d => F (z.1+z.2)) (volume.prod ν) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall fun a => ?_,havg⟩
    exact (integrable_norm_iff
      ((hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable)).mp (hlocal a)
  obtain ⟨x,hx⟩ := hi.prod_left_ae.exists
  exact ((measurePreserving_add_right (volume : Measure (Vec d)) x).integrable_comp
    hF.aestronglyMeasurable).mp hx

end EinsteinRelation.Correctors
