import EinsteinRelation.External.GantertSection7Support
import EinsteinRelation.Diffusion.FellerKernelUniquenessSupport
import EinsteinRelation.Probability.EquivDensityTransport
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.External.GantertSection7Support

/-- The physical force weight has the exact inverse-translation factor. -/
theorem physicalForceWeight_addLeft_symm {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ) (a x : Vec d) :
    physicalForceWeight hd lam ((MeasurableEquiv.addLeft a).symm x) =
      Real.exp (-2 * lam * a (firstCoordinateIndex hd)) * physicalForceWeight hd lam x := by
  unfold physicalForceWeight
  rw [← Real.exp_add]
  congr 1
  change 2 * lam * (-a (firstCoordinateIndex hd) + x (firstCoordinateIndex hd)) = _
  ring

/-- Source `paper/main.tex:406–408`: spatial translation changes the physical reversible measure by a positive constant. -/
theorem map_add_left_physicalReversibleMeasure {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (a : Vec d) :
    (physicalReversibleMeasure (translate a ω) hd lam).map (fun x => a + x) =
      ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd))) •
        physicalReversibleMeasure ω hd lam := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft a
  have hf : Measurable (fun x => ENNReal.ofReal
      (physicalReversibleDensity (translate a ω) hd lam x)) :=
    ENNReal.measurable_ofReal.comp (physicalReversibleDensity_continuous _ hd lam).measurable
  have hfo : Measurable (fun x => ENNReal.ofReal (physicalReversibleDensity ω hd lam x)) :=
    ENNReal.measurable_ofReal.comp (physicalReversibleDensity_continuous ω hd lam).measurable
  have hm : (volume : Measure (Vec d)).map e = volume := by
    simpa [e] using (measurePreserving_add_left (volume : Measure (Vec d)) a).map_eq
  change (volume.withDensity (fun x => ENNReal.ofReal
    (physicalReversibleDensity (translate a ω) hd lam x))).map e = _
  rw [EinsteinRelation.Probability.map_withDensity_equiv e _ _ hf, hm]
  have hden : (fun y => ENNReal.ofReal (physicalReversibleDensity (translate a ω) hd lam (e.symm y))) =
      ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd))) •
        (fun y => ENNReal.ofReal (physicalReversibleDensity ω hd lam y)) := by
    funext x
    have hclock : clockDensity (translate a ω) (e.symm x) = clockDensity ω x := by
      simp [clockDensity, translate, e]
    have hforce : physicalForceWeight hd lam (e.symm x) =
        Real.exp (-2 * lam * a (firstCoordinateIndex hd)) * physicalForceWeight hd lam x :=
      physicalForceWeight_addLeft_symm hd lam a x
    calc
      ENNReal.ofReal (physicalReversibleDensity (translate a ω) hd lam (e.symm x))
          = ENNReal.ofReal (physicalForceWeight hd lam (e.symm x) * clockDensity (translate a ω) (e.symm x)) := rfl
      _ = ENNReal.ofReal (physicalForceWeight hd lam (e.symm x) * clockDensity ω x) := by rw [hclock]
      _ = ENNReal.ofReal ((Real.exp (-2 * lam * a (firstCoordinateIndex hd)) * physicalForceWeight hd lam x) * clockDensity ω x) := by rw [hforce]
      _ = ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd)) * (physicalForceWeight hd lam x * clockDensity ω x)) := by ring_nf
      _ = ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd))) * ENNReal.ofReal (physicalForceWeight hd lam x * clockDensity ω x) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ = ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd))) • ENNReal.ofReal (physicalForceWeight hd lam x * clockDensity ω x) := by rfl
      _ = ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd))) • ENNReal.ofReal (physicalReversibleDensity ω hd lam x) := rfl
  rw [hden, withDensity_smul _ hfo]
  rfl

end EinsteinRelation.External.GantertSection7Support
