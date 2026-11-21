import EinsteinFull.External.DFGW.Semigroup
import MarkovProcess.Semigroup.Resolvent

/-! # Resolvent of the reversible semigroup

The positive-parameter resolvent is the Laplace transform of the reversible transition
semigroup. It is self-adjoint and has a nonnegative quadratic form.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The resolvent of the stationary transition semigroup. -/
noncomputable def transitionResolvent (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (lam : MarkovProcess.Semigroup.PositiveShift) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (transitionSemigroup hP).resolvent lam

/-- A resolvent pairing is the Laplace transform of the corresponding semigroup pairing. -/
theorem inner_transitionResolvent (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (lam : MarkovProcess.Semigroup.PositiveShift) (f g : Lp ℝ 2 μ) :
    inner ℝ f (transitionResolvent hP lam g) =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lam : ℝ) * t) *
        inner ℝ f (transitionSemigroup hP (Real.toNNReal t) g) := by
  rw [transitionResolvent, MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.resolvent_apply,
    ← integral_inner ((transitionSemigroup hP).integrableOn_laplaceIntegrand lam.2 g) f]
  apply integral_congr_ae
  filter_upwards with t
  simp only [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply,
    real_inner_smul_right]

/-- The resolvent of the reversible semigroup is self-adjoint. -/
theorem isSelfAdjoint_transitionResolvent (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (lam : MarkovProcess.Semigroup.PositiveShift) : IsSelfAdjoint (transitionResolvent hP lam) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℝ (transitionResolvent hP lam f) g =
    inner ℝ f (transitionResolvent hP lam g)
  rw [real_inner_comm g (transitionResolvent hP lam f),
    inner_transitionResolvent, inner_transitionResolvent]
  apply integral_congr_ae
  filter_upwards with t
  rw [show inner ℝ g (transitionSemigroup hP (Real.toNNReal t) f) =
    inner ℝ f (transitionSemigroup hP (Real.toNNReal t) g) by
      change inner ℝ g (transitionOperator hP (Real.toNNReal t) f) =
        inner ℝ f (transitionOperator hP (Real.toNNReal t) g)
      rw [← inner_transitionOperator hP (Real.toNNReal t) f g, real_inner_comm]]

/-- The resolvent of the reversible semigroup has nonnegative quadratic form. -/
theorem inner_transitionResolvent_nonneg (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (lam : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ) :
    0 ≤ inner ℝ f (transitionResolvent hP lam f) := by
  rw [inner_transitionResolvent]
  apply integral_nonneg
  intro t
  exact mul_nonneg (Real.exp_pos _).le (inner_transitionSemigroup_nonneg hP _ f)

end EinsteinFull.External.DFGW
