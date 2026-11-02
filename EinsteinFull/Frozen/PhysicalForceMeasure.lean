import EinsteinRelation.Environment.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- Physical-space measure exp(2*lambda*x_i) dx, with no environment-law weight. -/
noncomputable def physicalForceMeasure {d : ℕ} (i : Fin d) (lam : ℝ) : Measure (Vec d) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (2 * lam * x i)))

end EinsteinFull
