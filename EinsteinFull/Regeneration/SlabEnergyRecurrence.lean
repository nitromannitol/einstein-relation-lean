import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Arithmetic for the slab energy recurrence

The square-root error terms in Gantert–Mathieu–Piatnitski, equations
(4.15)–(4.19), reduce to a single affine energy recurrence.
-/

namespace EinsteinFull.Regeneration

/-- Bounds for the cutoff errors imply an affine bound for the inner energy. -/
theorem slab_energy_recurrence_of_error_bounds
    (A K L ε E T S N : ℝ) (hA : 0 ≤ A) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hTb : T ≤ A * ε + K * L ^ 2 * E) (hSb : S ≤ A * ε + K * E)
    (hN : N ≤ K * A * ε + K * ε ^ 2 * T +
      2 * K * ε * Real.sqrt T * Real.sqrt S) :
    N ≤ K * (4 * A + 3 * K + 1) * (ε + L ^ 2 * ε * E) := by
  have hK0 : 0 ≤ K := by linarith
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hP : 0 ≤ L ^ 2 * E := mul_nonneg (sq_nonneg L) hE
  have hEP : E ≤ L ^ 2 * E := by nlinarith
  have hS' : S ≤ A * ε + K * (L ^ 2 * E) := by
    linarith [mul_le_mul_of_nonneg_left hEP hK0]
  have hT' : T ≤ A * ε + K * (L ^ 2 * E) := by nlinarith [hTb]
  have hroot : 2 * Real.sqrt T * Real.sqrt S ≤ T + S := by
    nlinarith [sq_nonneg (Real.sqrt T - Real.sqrt S), Real.sq_sqrt hT,
      Real.sq_sqrt hS]
  have hepssq : ε ^ 2 ≤ ε := by nlinarith
  have hterm : K * ε ^ 2 * T ≤ K * ε * T := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hepssq hK0) hT
  have hrootterm : 2 * K * ε * Real.sqrt T * Real.sqrt S ≤ K * ε * (T + S) := by
    have h := mul_le_mul_of_nonneg_left hroot (mul_nonneg hK0 hε)
    nlinarith
  have hsum : 2 * T + S ≤ 3 * (A * ε + K * (L ^ 2 * E)) := by linarith
  have hsum' : K * ε * (2 * T + S) ≤
      K * ε * (3 * (A * ε + K * (L ^ 2 * E))) :=
    mul_le_mul_of_nonneg_left hsum (mul_nonneg hK0 hε)
  have hAeps : A * ε ≤ A := by
    simpa using mul_le_mul_of_nonneg_left hε1 hA
  have hmain : N ≤ K * ε * (4 * A + 3 * K * (L ^ 2 * E)) := by
    have h := mul_le_mul_of_nonneg_left hAeps (mul_nonneg hK0 hε)
    nlinarith [hN, hterm, hrootterm, hsum']
  have hcomp : 4 * A + 3 * K * (L ^ 2 * E) ≤
      (4 * A + 3 * K + 1) * (1 + L ^ 2 * E) := by
    nlinarith [mul_nonneg hA hP, mul_nonneg hK0 hP]
  have hlast := mul_le_mul_of_nonneg_left hcomp (mul_nonneg hK0 hε)
  nlinarith [hmain, hlast]

end EinsteinFull.Regeneration
