import EinsteinRelation.Diffusion.ForceMeasureLpTranslation
import EinsteinRelation.Diffusion.TranslatedReversibleMeasure
import EinsteinRelation.Probability.EquivDensityTransport
import EinsteinRelation.Diffusion.ConjugatedFormQuotient

/-! # Translation of the exponential force measure

Source `paper/main.tex:406–408`. The force density changes by one
strictly positive constant, so every weighted `Lp` membership is preserved.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.External.GantertSection7Support

/-- Translation rescales the actual exponential force measure. -/
theorem map_add_left_physicalForceMeasure {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ) (a : Vec d) :
    (physicalForceMeasure hd lam).map (MeasurableEquiv.addLeft a) =
      ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd))) •
        physicalForceMeasure hd lam := by
  have hf : Measurable (fun x => ENNReal.ofReal (physicalForceWeight hd lam x)) :=
    ENNReal.measurable_ofReal.comp (physicalForceWeight_continuous hd lam).measurable
  have hm : (volume : Measure (Vec d)).map (MeasurableEquiv.addLeft a) = volume :=
    (measurePreserving_add_left volume a).map_eq
  unfold physicalForceMeasure
  rw [Probability.map_withDensity_equiv _ _ _ hf,
    hm]
  have hden : (fun y => ENNReal.ofReal
      (physicalForceWeight hd lam ((MeasurableEquiv.addLeft a).symm y))) =
      ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd))) •
        (fun y => ENNReal.ofReal (physicalForceWeight hd lam y)) := by
    funext x
    rw [physicalForceWeight_addLeft_symm, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rfl
  rw [hden, withDensity_smul _ hf]


end EinsteinRelation.External.GantertSection7Support
