import EinsteinFull.External.DFGW.DriftVarianceLimit
import EinsteinFull.External.DFGW.FiniteTimeVariance
import EinsteinFull.External.DFGW.ProjectedVelocityCorrelation

/-! # Long-time variance of projected increments

The projected increment variance has a finite long-time limit given by the martingale
second moment and the integrated velocity autocorrelation.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The normalized projected increment variance converges to the martingale variance minus
twice the velocity autocorrelation integral. -/
theorem tendsto_normalized_dot_increment_sq
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) (e : Vec d)
    (hg : MemLp (fun x => dot e (φ x)) 2 μ) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ η : C(ℝ, S), dot e (X 0 t η) ^ 2 ∂P) atTop
      (𝓝 (dot e ((secondMomentMatrix P (compensated X φ 1)).mulVec e) -
        2 * ∫ t in Set.Ioi (0 : ℝ), inner ℝ (hg.toLp (fun x => dot e (φ x)))
          (transitionOperator hP t.toNNReal (hg.toLp (fun x => dot e (φ x)))))) := by
  have hint := integrableOn_projected_velocity_autocorrelation hP hX φ hφ hlim hL2 hM e hg
  have hdrift := tendsto_normalized_time_integral_sq hP (fun x => dot e (φ x)) hg hint
  have h := (tendsto_const_nhds (x :=
    dot e ((secondMomentMatrix P (compensated X φ 1)).mulVec e))).sub hdrift
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hfinite := integral_dot_increment_sq_eq_martingale_sub_drift hP hX φ hφ hL2 hM t.toNNReal e
  rw [Real.coe_toNNReal _ ht.le] at hfinite
  rw [hfinite]
  field_simp

end EinsteinFull.External.DFGW
