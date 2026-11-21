import EinsteinFull.External.DFGW.ResolventMartingaleCauchy

/-! # Fixed-time limits of resolvent martingales

The square-integrable resolvent martingale approximations have a unique limit at each fixed
time when the observable has integrable autocorrelation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The fixed-time `L²` limit of the resolvent Dynkin martingale increments exists uniquely. -/
theorem existsUnique_resolvent_dynkinIncrement_limit
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (t : ℝ≥0) :
    ∃! Z : Lp ℝ 2 P, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 Z) := by
  obtain ⟨Z, hZ⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_resolvent_dynkinIncrement hP hcoord f hint t)
  exact ⟨Z, hZ, fun W hW => tendsto_nhds_unique hW hZ⟩

/-- There is a unique `L²` limit for the resolvent martingale at every time simultaneously. -/
theorem existsUnique_resolvent_dynkinIncrement_family
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    ∃! Z : ℝ≥0 → Lp ℝ 2 P, ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)) := by
  have hex : ∀ t, ∃! Z : Lp ℝ 2 P, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 Z) :=
    existsUnique_resolvent_dynkinIncrement_limit hP hcoord f hint
  choose Z hZ using fun t => (hex t).exists
  refine ⟨Z, hZ, ?_⟩
  intro W hW
  funext t
  exact tendsto_nhds_unique (hW t) (hZ t)

end EinsteinFull.External.DFGW
