import EinsteinFull.Calculus.S4CoefficientFamilySupport
import EinsteinRelation.Localization.CoefficientObservations

/-!
# `FieldPair d` is a Polish space

Used locally (`letI := fieldPair_polish d`); not a global instance, to avoid uniform-structure
diamonds on `Mat d`.
-/

open EinsteinRelation

namespace EinsteinFull

theorem fieldPair_polish (d : ℕ) : PolishSpace (FieldPair d) := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  infer_instance

end EinsteinFull
