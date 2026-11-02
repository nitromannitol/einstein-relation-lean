import EinsteinRelation.External.AKMLocalCorrectors
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM
/-- Scalar homogeneity of the normalized square mean (`paper/main.tex:938–945`). -/
theorem scalarRms_const_mul_abs {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (U : Set X) (c : ℝ) (f : X → ℝ) :
    scalarRms ν U (fun x => c * f x) = |c| * scalarRms ν U f := by
  unfold scalarRms
  have hsq : (⨍ x in U, (c * f x) ^ 2 ∂ν) = c ^ 2 * ⨍ x in U, (f x) ^ 2 ∂ν := by
    simp only [mul_pow, average_eq, smul_eq_mul, integral_const_mul]
    ring
  rw [hsq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
end EinsteinRelation.Correctors
