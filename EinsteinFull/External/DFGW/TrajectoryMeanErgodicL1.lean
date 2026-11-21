import EinsteinFull.External.DFGW.TrajectoryMeanErgodic
import EinsteinFull.External.DFGW.L1ShiftOperator
import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-! # `L¹` mean ergodic theorem for trajectory shifts

The `L²` mean ergodic theorem extends by density and uniform contraction to every integrable
trajectory observable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- `L¹` averages of a positive trajectory shift converge to the mean projection. -/
theorem tendsto_shift_birkhoffAverage_L1 (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤) {t : ℝ≥0} (ht : 0 < t)
    (f : Lp ℝ 1 P) :
    Tendsto (birkhoffAverage ℝ (trajectoryShiftOperatorL1 hP t) id · f) atTop
      (𝓝 (trajectoryMeanOperator hP hPfin f)) := by
  let : IsProbabilityMeasure P := hP.probability
  let U := trajectoryShiftOperator hP t
  let V := trajectoryShiftOperatorL1 hP t
  let J := lpTwoToOne P
  let M := trajectoryMeanOperator hP hPfin
  have hlip : LipschitzWith 1 V :=
    ContinuousLinearMap.lipschitzWith_of_opNorm_le (by
      simpa only [NNReal.coe_one] using norm_trajectoryShiftOperatorL1_le_one hP t)
  have hclosed : IsClosed {g : Lp ℝ 1 P |
      Tendsto (birkhoffAverage ℝ V id · g) atTop (𝓝 (M g))} :=
    isClosed_setOfPred_tendsto_birkhoffAverage ℝ hlip uniformContinuous_id M.continuous
  have hrange : ∀ g ∈ Set.range J,
      Tendsto (birkhoffAverage ℝ V id · g) atTop (𝓝 (M g)) := by
    rintro _ ⟨z, rfl⟩
    have hit (k : ℕ) : J (U^[k] z) = V^[k] (J z) := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
        exact lpTwoToOne_shift hP t (U^[k] z)
    have havg (n : ℕ) : J (birkhoffAverage ℝ U id n z) =
        birkhoffAverage ℝ V id n (J z) := by
      simp only [birkhoffAverage, birkhoffSum, id_eq, map_smul, map_sum, hit]
    have h2 := tendsto_shift_birkhoffAverage_L2 hP hcoord hμ hPfin ht z
    change Tendsto (birkhoffAverage ℝ U id · z) atTop
      (𝓝 (indicatorConstLp 2 MeasurableSet.univ hPfin (∫ η, z η ∂P))) at h2
    have h := (J.continuous.tendsto _).comp h2
    have hM : J (indicatorConstLp 2 MeasurableSet.univ hPfin (∫ η, z η ∂P)) = M (J z) :=
      (trajectoryMeanOperator_lpTwoToOne hP hPfin z).symm
    simpa only [Function.comp_def, havg, hM] using h
  exact (denseRange_lpTwoToOne P).induction hrange hclosed f

end EinsteinFull.External.DFGW
