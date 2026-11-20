import EinsteinFull.External.DFGW.ProjectionVariance
import EinsteinFull.External.DFGW.AdditiveVariance

/-! # Finite-time variance formula

Reflection and stationary martingale increments express the variance of an increment as its
martingale variance less the integrated drift variance.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The second moment of a projected increment equals the linearly growing compensated
second moment less the second moment of the projected integrated drift. -/
theorem integral_dot_increment_sq_eq_martingale_sub_drift
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (t : ℝ≥0) (e : Vec d) :
    (∫ η, dot e (X 0 t η) ^ 2 ∂P) =
      (t : ℝ) * dot e ((secondMomentMatrix P (compensated X φ 1)).mulVec e) -
        ∫ η, (∫ u in (0 : ℝ)..(t : ℝ), dot e (φ (η u))) ^ 2 ∂P := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  have hlin := integral_projected_compensated_sq_eq_mul hP hX φ
    (hφ.integrable one_le_two) hL2 hM L t
  simp only [hL] at hlin
  have hpyth := integral_dot_increment_sq_add_drift_sq hP hX φ hφ t (hL2 t) e
  rw [secondMomentMatrix_quadratic P _ (hL2 1) e]
  linarith

end EinsteinFull.External.DFGW
