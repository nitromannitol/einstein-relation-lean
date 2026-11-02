import EinsteinFull.Frozen.PhysicalForceMeasure

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- Positive physical gauge weights have exactly the Lebesgue null sets. -/
theorem physicalForceMeasure_absolutelyContinuous {d : ℕ} (i : Fin d) (lam : ℝ) :
    physicalForceMeasure i lam ≪ (volume : Measure (Vec d)) :=
  withDensity_absolutelyContinuous _ _

theorem volume_absolutelyContinuous_physicalForceMeasure {d : ℕ}
    (i : Fin d) (lam : ℝ) :
    (volume : Measure (Vec d)) ≪ physicalForceMeasure i lam := by
  unfold physicalForceMeasure
  apply withDensity_absolutelyContinuous'
  · exact (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_apply i)))).measurable.aemeasurable
  · exact Filter.Eventually.of_forall fun x => by
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- At zero force the physical reference measure is exactly Lebesgue measure. -/
theorem physicalForceMeasure_zero {d : ℕ} (i : Fin d) :
    physicalForceMeasure i 0 = (volume : Measure (Vec d)) := by
  simp [physicalForceMeasure]

end EinsteinFull
