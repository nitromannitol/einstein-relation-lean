import EinsteinFull.Calculus.C6FluxActualRecoveryPartitions

namespace EinsteinFull.Blueprint
open EinsteinRelation

theorem c6_actual_schwartz_recovery_coefficient_budget
    (d : ℕ) (Crec Csite : ℝ) (hCrec : 1 ≤ Crec) (hCsite : 0 < Csite) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s r ctest : ℝ) (hs : 0 < s) (hr : 0 < r)
      (hctest : 0 < ctest) (k : ℕ) (z : Vec d),
    let R := 2 * Real.sqrt (d : ℝ) + 2
    let E := sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y-z) ≤ R*r})
    let W := s ^ (-(k : ℝ) / 2) * E
    let M : Bool → ℝ := fun b => 2 * Crec *
      (1 + Csite + Csite * (R + r * (Real.sqrt s)⁻¹)) *
        (if b then r ^ d else r ^ (d+1))
    W * (4 * M true * r ^ (-(d : ℝ)) +
      4 * M false * r ^ (-(d : ℝ)-1)) ≤
      C * s ^ (-(k : ℝ)/2) * E * (1 + r / Real.sqrt s) := by
  let R : ℝ := 2 * Real.sqrt (d : ℝ) + 2
  let A : ℝ := 1 + Csite + Csite * R
  refine ⟨16 * Crec * (A + Csite), by dsimp [A, R]; positivity, ?_⟩
  intro s r ctest hs hr hctest k z
  dsimp only
  have hR : 0 ≤ R * r := by dsimp [R]; positivity
  have hsup := c1_gaussian_ball_sup s ctest (R * r) hs hctest hR z
  have hz : z ∈ {y : Vec d | euclideanNorm (y - z) ≤ R * r} := by
    simpa [euclideanNorm, euclideanSq, dot] using hR
  have hE : 0 ≤ sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y-z) ≤ R*r}) :=
    le_trans (by positivity) (hsup.2 z hz)
  have hp₁ : r ^ d * r ^ (-(d : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    simp
  have hp₂ : r ^ (d+1) * r ^ (-(d : ℝ)-1) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    push_cast
    simp
  have ht : 0 ≤ r * (Real.sqrt s)⁻¹ := by positivity
  have hA : 0 ≤ A := by dsimp [A, R]; positivity
  have hcoef : 1 + Csite + Csite * (R + r * (Real.sqrt s)⁻¹) ≤
      (A + Csite) * (1 + r * (Real.sqrt s)⁻¹) := by
    dsimp [A] at *
    nlinarith [mul_nonneg hA ht, mul_nonneg hCsite.le ht]
  have hW : 0 ≤ s ^ (-(k : ℝ) / 2) * sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y-z) ≤ R*r}) := mul_nonneg (Real.rpow_nonneg hs.le _) hE
  have hmul := mul_le_mul_of_nonneg_left hcoef (mul_nonneg (by positivity : 0 ≤ 16 * Crec) hW)
  have hcancel : 4 * (2 * Crec * (1 + Csite + Csite * (R + r * (Real.sqrt s)⁻¹)) * r ^ d) * r ^ (-(d : ℝ)) +
      4 * (2 * Crec * (1 + Csite + Csite * (R + r * (Real.sqrt s)⁻¹)) * r ^ (d+1)) * r ^ (-(d : ℝ)-1) =
      16 * Crec * (1 + Csite + Csite * (R + r * (Real.sqrt s)⁻¹)) := by
    calc
      _ = 8 * Crec * (1 + Csite + Csite * (R + r * (Real.sqrt s)⁻¹)) *
          (r ^ d * r ^ (-(d : ℝ)) + r ^ (d+1) * r ^ (-(d : ℝ)-1)) := by ring
      _ = _ := by rw [hp₁, hp₂]; ring
  dsimp [R] at *
  simp only [div_eq_mul_inv] at *
  rw [hcancel]
  convert hmul using 1 <;> ring

end EinsteinFull.Blueprint
