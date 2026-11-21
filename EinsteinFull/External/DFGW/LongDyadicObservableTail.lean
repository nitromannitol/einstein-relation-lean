import EinsteinFull.External.DFGW.DyadicBlockDecomposition
import EinsteinFull.External.DFGW.StationaryDyadicBlockTail

/-! # Fixed-observable tails on long dyadic grids

Stationarity and square-integrable unit-block maxima make a fixed generator-domain observable
negligible at diffusive scale uniformly over dyadic points on a growing interval.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The maximum of a fixed generator-domain observable on the dyadic grid of `[0,n]` is
`o(√n)` in probability. -/
theorem tendsto_measureReal_max_dyadic_observable_long_interval
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {η | ∃ r j, j ≤ 2 ^ r ∧
      δ * n ≤ |(f : Lp ℝ 2 μ) (η (dyadicGridTime (n : ℝ≥0) r j))| ^ 2}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  have htail := (tendsto_measureReal_max_dyadic_observable_blocks hP hcoord f
    (δ := δ / 2) (by positivity)).comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ htail
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hthreshold : (δ / 2) * (n + 1 : ℕ) ≤ δ * n := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  simp only [Function.comp_apply]
  apply measureReal_mono _ (measure_ne_top P _)
  intro η hη
  obtain ⟨r, j, hj, hval⟩ := hη
  obtain ⟨k, l, hk, hl, heq⟩ := dyadicGridTime_nat_eq_block n r j hj
  refine ⟨k, Nat.lt_succ_of_le hk, r, l, hl, ?_⟩
  have htime : (dyadicGridTime (n : ℝ≥0) r j : ℝ) =
      (k : ℝ) + (dyadicGridTime 1 r l : ℝ) := by exact_mod_cast heq
  rw [htime] at hval
  exact le_trans hthreshold hval

end EinsteinFull.External.DFGW
