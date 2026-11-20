import EinsteinFull.External.DFGW.ResolventDifference

/-! # Generator energy of resolvent differences

A difference of reversible resolvents has energy bounded by the difference of their quadratic
pairings.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The energy of a resolvent difference is bounded by a difference of resolvent pairings. -/
theorem transitionResolvent_difference_energy_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (a b : MarkovProcess.Semigroup.PositiveShift) (hab : (a : ℝ) ≤ b) (f : Lp ℝ 2 μ) :
    -inner ℝ (transitionResolvent hP a f - transitionResolvent hP b f)
      ((a : ℝ) • transitionResolvent hP a f - (b : ℝ) • transitionResolvent hP b f) ≤
      inner ℝ f (transitionResolvent hP a f) - inner ℝ f (transitionResolvent hP b f) := by
  let A := transitionResolvent hP a
  let B := transitionResolvent hP b
  have hd : A f - B f = ((b : ℝ) - a) • A (B f) := by
    have h := congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => L f)
      ((transitionSemigroup hP).resolvent_sub_resolvent a b)
    dsimp only [A, B, transitionResolvent]
    simpa only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] using h
  have hsym : inner ℝ f (A (B f)) = inner ℝ (A f) (B f) := by
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_transitionResolvent hP a)) f (B f)).symm
  have hid : inner ℝ f (A f) - inner ℝ f (B f) =
      ((b : ℝ) - a) * inner ℝ (A f) (B f) := by
    rw [← inner_sub_right, hd, real_inner_smul_right, hsym]
  have hsq : 0 ≤ ‖A f‖ ^ 2 + ‖B f‖ ^ 2 - 2 * inner ℝ (A f) (B f) := by
    have h := sq_nonneg ‖A f - B f‖
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    simp only [show inner ℝ (B f) (A f) = inner ℝ (A f) (B f) from
      (real_inner_comm (B f) (A f)).symm] at h
    linarith
  have hsq' := mul_nonneg a.2.le hsq
  have hweight := mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg ‖B f‖)
  change -inner ℝ (A f - B f) ((a : ℝ) • A f - (b : ℝ) • B f) ≤
    inner ℝ f (A f) - inner ℝ f (B f)
  rw [hid, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  simp only [show inner ℝ (B f) (A f) = inner ℝ (A f) (B f) from
    (real_inner_comm (B f) (A f)).symm]
  nlinarith

end EinsteinFull.External.DFGW
