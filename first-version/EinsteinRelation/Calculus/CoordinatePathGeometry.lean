import EinsteinRelation.Calculus.CoordinateTranslationPath
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-! # Euclidean geometry of the coordinate paths

Source: `paper/main.tex:1021–1029,1079–1084`. Every partial coordinate
segment stays inside the Euclidean ball of its final displacement.
-/

noncomputable section
namespace EinsteinRelation

/-- A coordinate path never increases the Euclidean radius
(`paper/main.tex:1021–1029,1079–1084`). -/
theorem euclideanNorm_coordinateSegment_bound {d : ℕ} (z : Vec d) (i : Fin d)
    {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) (z i)) :
    euclideanNorm (coordinateSegment z i t) ≤ euclideanNorm z := by
  have hat : |t| ≤ |z i| := by simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc ht
  have hsq : t * t ≤ z i * z i := by
    have hh := mul_self_le_mul_self (abs_nonneg t) hat
    simpa only [← sq, sq_abs] using hh
  apply Real.sqrt_le_sqrt
  unfold euclideanSq dot
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j = i
  · subst j
    simpa [coordinateSegment, coordinatePrefix, unitVector] using hsq
  · by_cases hj : j.val < i.val
    · simp [coordinateSegment, coordinatePrefix, unitVector, hj, hji]
    · simp only [coordinateSegment, coordinatePrefix, hj, if_false, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, unitVector, Pi.single_eq_of_ne hji]
      nlinarith [mul_self_nonneg (z j)]

end EinsteinRelation
