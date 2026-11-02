import EinsteinRelation.Environment.Reduction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Deterministic bounds after moving the potential into the coefficient -/

namespace EinsteinRelation

/-- The pointwise exponential bounds supplied by the bounded potential. -/
theorem clockDensity_bounds {d : ℕ} (ω : FieldPair d) (x : Vec d) (L : ℝ)
    (hV : |ω.2 x| ≤ L) :
    Real.exp (-2 * L) ≤ clockDensity ω x ∧ clockDensity ω x ≤ Real.exp (2 * L) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hV
  constructor
  · apply Real.exp_le_exp.mpr
    linarith
  · apply Real.exp_le_exp.mpr
    linarith

/-- Symmetry is preserved by the time change, with no isotropy assumption. -/
theorem reducedCoefficient_transpose {d : ℕ} (ω : FieldPair d) (x : Vec d)
    (hsymm : (ω.1 x).transpose = ω.1 x) :
    (reducedCoefficient ω x).transpose = reducedCoefficient ω x := by
  rw [reducedCoefficient, Matrix.transpose_smul, hsymm]

/-- The exact scaling of the quadratic form by the clock density. -/
theorem reducedCoefficient_energy {d : ℕ} (ω : FieldPair d) (x ξ : Vec d) :
    dot ξ ((reducedCoefficient ω x).mulVec ξ) =
      clockDensity ω x * dot ξ ((ω.1 x).mulVec ξ) := by
  change dotProduct ξ ((clockDensity ω x • ω.1 x).mulVec ξ) =
    clockDensity ω x * dotProduct ξ ((ω.1 x).mulVec ξ)
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Euclidean ellipticity constants depending only on the original bound. -/
theorem reducedCoefficient_energy_bounds {d : ℕ} (ω : FieldPair d) (x ξ : Vec d)
    (L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) :
    (Real.exp (-2 * L) * L⁻¹) * euclideanSq ξ ≤
        dot ξ ((reducedCoefficient ω x).mulVec ξ) ∧
    dot ξ ((reducedCoefficient ω x).mulVec ξ) ≤
        (Real.exp (2 * L) * L) * euclideanSq ξ := by
  have hsq : 0 ≤ euclideanSq ξ := by
    change 0 ≤ ∑ i, ξ i * ξ i
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (ξ i))
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hclock := clockDensity_bounds ω x L (hω.2.1 x)
  obtain ⟨hlo, hhi⟩ := (hω.1 x).2 ξ
  rw [reducedCoefficient_energy]
  constructor
  · calc
      _ = Real.exp (-2 * L) * (L⁻¹ * euclideanSq ξ) := by ring
      _ ≤ clockDensity ω x * (L⁻¹ * euclideanSq ξ) :=
        mul_le_mul_of_nonneg_right hclock.1 (mul_nonneg (inv_nonneg.mpr hL0) hsq)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (clockDensity_pos ω x).le
  · calc
      _ ≤ clockDensity ω x * (L * euclideanSq ξ) :=
        mul_le_mul_of_nonneg_left hhi (clockDensity_pos ω x).le
      _ ≤ Real.exp (2 * L) * (L * euclideanSq ξ) :=
        mul_le_mul_of_nonneg_right hclock.2 (mul_nonneg hL0 hsq)
      _ = _ := by ring

end EinsteinRelation
