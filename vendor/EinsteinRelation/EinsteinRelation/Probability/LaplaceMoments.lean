import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Scalar moments of the exponential resolvent weight

`paper/main.tex:493–500` (`regen.occupation-resolvent`) uses these exact
moments after the time occupation bound. They do not establish the occupation
bound or an Abel limit by themselves.
-/

open MeasureTheory Set

namespace EinsteinRelation.Probability

/-- The exponential time density has total mass one. -/
theorem laplace_mass (s : ℝ) (hs : 0 < s) :
    s * (∫ t : ℝ in Ioi 0, Real.exp (-s * t)) = 1 := by
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hs)]
  simp [ne_of_gt hs]

/-- The first exponential moment has the normalization used in the Abel formula. -/
theorem laplace_first_moment (s : ℝ) (hs : 0 < s) :
    s ^ 2 * (∫ t : ℝ in Ioi 0, t * Real.exp (-s * t)) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := (1 : ℝ)) (b := s) (by norm_num) (by norm_num) hs
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    simp
  norm_num [Real.rpow_one, hg] at h
  simp only [neg_mul]
  rw [h]
  exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hs))

/-- Algebra after inserting the two exponential moments in the occupation bound. -/
theorem occupation_laplace_constant (s Δ C : ℝ) (hs : 0 < s) :
    s ^ 2 * (C * ((s ^ 2)⁻¹ + Δ * s⁻¹)) = C * (1 + s * Δ) := by
  field_simp [ne_of_gt hs]

end EinsteinRelation.Probability
