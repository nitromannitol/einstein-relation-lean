import EinsteinFull.External.DFGW.OpenStrong
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! # Strongly continuous vectors

Vectors whose transition orbit is strongly continuous at zero form a closed linear subspace.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The vectors with a strongly continuous transition orbit at time zero. -/
def continuousVectors (hP : Draft.IsDFGWTrajectoryProcess P μ T) : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f | Tendsto (fun t : ℝ≥0 => transitionOperator hP t f) (𝓝 0) (𝓝 f)}
  zero_mem' := by
    change Tendsto (fun t : ℝ≥0 => transitionOperator hP t 0) (𝓝 0) (𝓝 0)
    simpa only [map_zero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℝ≥0 => (0 : Lp ℝ 2 μ)) (𝓝 0) (𝓝 0))
  add_mem' := by
    intro f g hf hg
    change Tendsto (fun t : ℝ≥0 => transitionOperator hP t (f + g)) (𝓝 0) (𝓝 (f + g))
    simpa only [map_add] using hf.add hg
  smul_mem' := by
    intro c f hf
    change Tendsto (fun t : ℝ≥0 => transitionOperator hP t (c • f)) (𝓝 0) (𝓝 (c • f))
    simpa only [map_smul] using hf.const_smul c

/-- The strongly continuous vectors form a closed subspace. -/
theorem isClosed_continuousVectors (hP : Draft.IsDFGWTrajectoryProcess P μ T) :
    IsClosed (continuousVectors hP : Set (Lp ℝ 2 μ)) := by
  have heq : UniformEquicontinuous (fun t : ℝ≥0 => transitionOperator hP t) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε, hε, fun f g hfg t => ?_⟩
    have hn : ‖transitionOperator hP t‖ ≤ ((1 : ℝ≥0) : ℝ) := by
      simpa only [NNReal.coe_one] using norm_transitionOperator_le_one hP t
    have hlip : LipschitzWith 1 (transitionOperator hP t) :=
      ContinuousLinearMap.lipschitzWith_of_opNorm_le hn
    have hd : dist (transitionOperator hP t f) (transitionOperator hP t g) ≤ dist f g := by
      simpa only [NNReal.coe_one, one_mul] using hlip.dist_le_mul f g
    exact hd.trans_lt hfg
  exact heq.equicontinuous.isClosed_setOfPred_tendsto continuous_id

/-- Every open-set indicator belongs to the strongly continuous subspace. -/
theorem indicator_mem_continuousVectors (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {A : Set S} (hA : IsOpen A) (hμA : μ A ≠ ∞) :
    indicatorConstLp 2 hA.measurableSet hμA (1 : ℝ) ∈ continuousVectors hP :=
  tendsto_transitionOperator_open_indicator hP hA hμA

end EinsteinFull.External.DFGW
