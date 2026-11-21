import EinsteinFull.External.DFGW.Resolvent

/-! # Resolvent difference and norm bound

For a reversible contraction semigroup, the difference of two resolvent pairings controls
the norm of the resolvent at the larger parameter.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The resolvent identity bounds the larger-parameter resolvent norm by the difference of
quadratic resolvent pairings. -/
theorem mul_norm_transitionResolvent_sq_le_sub
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (a b : MarkovProcess.Semigroup.PositiveShift) (hab : (a : ℝ) ≤ b) (f : Lp ℝ 2 μ) :
    ((b : ℝ) - a) * ‖transitionResolvent hP b f‖ ^ 2 ≤
      inner ℝ f (transitionResolvent hP a f) - inner ℝ f (transitionResolvent hP b f) := by
  let A := transitionResolvent hP a
  let B := transitionResolvent hP b
  have hd : A f - B f = ((b : ℝ) - a) • A (B f) := by
    have h := congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => L f)
      ((transitionSemigroup hP).resolvent_sub_resolvent a b)
    dsimp only [A, B, transitionResolvent]
    simpa only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] using h
  have hpos : 0 ≤ inner ℝ (B f) (A (B f)) := inner_transitionResolvent_nonneg hP a (B f)
  have hnonneg : 0 ≤ inner ℝ (B f) (A f - B f) := by
    rw [hd, real_inner_smul_right]
    exact mul_nonneg (sub_nonneg.mpr hab) hpos
  have hsym : inner ℝ f (A (B f)) = inner ℝ (B f) (A f) := by
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_transitionResolvent hP a)) f (B f)
    change inner ℝ (A f) (B f) = inner ℝ f (A (B f)) at h
    rw [← h, real_inner_comm]
  have hid : inner ℝ f (A f) - inner ℝ f (B f) =
      ((b : ℝ) - a) * inner ℝ (B f) (A f) := by
    rw [← inner_sub_right, hd, real_inner_smul_right, hsym]
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hnonneg
  have hmul := mul_nonneg (sub_nonneg.mpr hab) hnonneg
  rw [hid]
  nlinarith

end EinsteinFull.External.DFGW
