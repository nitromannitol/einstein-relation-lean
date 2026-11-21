import EinsteinFull.External.DFGW.AllContinuousVectors
import MarkovProcess.Semigroup.OrbitContinuity

/-! # The reversible `L²` semigroup

The stationary reversible Markov process induces a strongly continuous contraction semigroup
whose operators are self-adjoint and nonnegative.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The strongly continuous contraction semigroup of the stationary process on `L²`. -/
noncomputable def transitionSemigroup (hP : Draft.IsDFGWTrajectoryProcess P μ T) :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ) :=
  MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.ofTendstoZero
    (transitionOperator hP) (transitionOperator_zero hP) (transitionOperator_add hP)
    (norm_transitionOperator_le_one hP) (tendsto_transitionOperator_zero hP)

/-- The semigroup operator is represented by the transition-kernel integral. -/
theorem transitionSemigroup_ae_eq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) :
    transitionSemigroup hP t f =ᵐ[μ] fun x => ∫ y, f y ∂T t x :=
  transitionOperator_ae_eq hP t f

/-- Each semigroup operator is self-adjoint. -/
theorem isSelfAdjoint_transitionSemigroup (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) : IsSelfAdjoint (transitionSemigroup hP t) :=
  isSelfAdjoint_transitionOperator hP t

/-- Each semigroup operator has a nonnegative quadratic form. -/
theorem inner_transitionSemigroup_nonneg (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) : 0 ≤ inner ℝ f (transitionSemigroup hP t f) :=
  inner_transitionOperator_nonneg hP t f

end EinsteinFull.External.DFGW
