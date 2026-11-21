import EinsteinFull.External.DFGW.TrajectoryShiftOperator
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-! # Mean ergodic theorem for trajectory shifts

Positive-time shift averages converge in `L²` to the trajectory observable's mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- `L²` averages of a positive trajectory shift converge to the mean. -/
theorem tendsto_shift_birkhoffAverage_L2 (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤) {t : ℝ≥0} (ht : 0 < t)
    (f : Lp ℝ 2 P) :
    Tendsto (birkhoffAverage ℝ (trajectoryShiftOperator hP t) id · f) atTop
      (𝓝 (indicatorConstLp 2 MeasurableSet.univ hPfin (∫ η, f η ∂P))) := by
  let : IsProbabilityMeasure P := hP.probability
  let U := trajectoryShiftOperator hP t
  let K := U.eqLocus (1 : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P)
  let p := K.orthogonalProjectionOnto f
  have hpfix : U p = p := p.property
  let one : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ hPfin 1
  have honefix : U one = one := trajectoryShiftOperator_const hP hPfin t 1
  have honeK : one ∈ K := honefix
  have hinner : inner ℝ one p = inner ℝ one f := by
    have hp := K.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨one, honeK⟩ f
    change inner ℝ (p : Lp ℝ 2 P) one = inner ℝ f one at hp
    exact (real_inner_comm (p : Lp ℝ 2 P) one).trans (hp.trans (real_inner_comm one f))
  have hpeq : (p : Lp ℝ 2 P) = indicatorConstLp 2 MeasurableSet.univ hPfin (∫ η, f η ∂P) :=
    fixed_shift_eq_mean_of_inner_one hP hcoord hμ hPfin ht p f hpfix hinner
  have h := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection U
    (norm_trajectoryShiftOperator_le_one hP t) f
  change Tendsto (birkhoffAverage ℝ U id · f) atTop (𝓝 (p : Lp ℝ 2 P)) at h
  rw [hpeq] at h
  exact h

end EinsteinFull.External.DFGW
