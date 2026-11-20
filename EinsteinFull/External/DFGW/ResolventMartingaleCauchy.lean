import EinsteinFull.External.DFGW.ResolventMartingale
import EinsteinFull.External.DFGW.VelocityResolventEnergy

/-! # Convergence of resolvent martingale increments

Integrable autocorrelations make the resolvent Dynkin martingale increments Cauchy in trajectory
`L²` at every fixed time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Resolvent Dynkin increments form a Cauchy sequence in `L²` at every fixed time. -/
theorem cauchySeq_resolvent_dynkinIncrement (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (t : ℝ≥0) :
    CauchySeq (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hden : 0 < 2 * (t : ℝ) + 1 := by positivity
  have hε' : 0 < ε ^ 2 / (2 * (t : ℝ) + 1) := div_pos (sq_pos_of_pos hε) hden
  obtain ⟨N, hN⟩ := resolvent_energy_cauchy hP f hint _ hε'
  refine ⟨N, fun n hn m hm => ?_⟩
  let F := transitionResolventDomain hP (reciprocalShift n) f -
    transitionResolventDomain hP (reciprocalShift m) f
  have henergy : -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F) <
      ε ^ 2 / (2 * (t : ℝ) + 1) := hN n hn m hm
  have hnonneg := generator_energy_nonneg hP F
  have hbound := (lt_div_iff₀ hden).mp henergy
  have hnorm := norm_dynkinIncrementLp_sub_sq hP hcoord
    (transitionResolventDomain hP (reciprocalShift n) f)
    (transitionResolventDomain hP (reciprocalShift m) f) t
  rw [dist_eq_norm]
  have hsquare : ‖dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift n) f) t -
      dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift m) f) t‖ ^ 2 < ε ^ 2 := by
    rw [hnorm]
    nlinarith
  have hnorm0 := norm_nonneg (dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift n) f) t -
    dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift m) f) t)
  nlinarith

end EinsteinFull.External.DFGW
