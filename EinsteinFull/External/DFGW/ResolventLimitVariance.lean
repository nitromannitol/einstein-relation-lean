import EinsteinFull.External.DFGW.ResolventEnergyLimit

/-! # Variance of the limiting resolvent martingale

The second moment of the limiting martingale is twice time times the integrated stationary
autocorrelation of the original observable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The squared norm of an `L²` Dynkin increment is twice time times generator energy. -/
theorem norm_dynkinIncrementLp_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    ‖dynkinIncrementLp hP f t‖ ^ 2 = (t : ℝ) *
      (2 * -inner ℝ (f : Lp ℝ 2 μ) ((transitionSemigroup hP).generator f)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hm : dynkinIncrementLp hP f t =ᵐ[P]
      fun η => dynkinProcess hP f t η - dynkinProcess hP f 0 η :=
    MemLp.coeFn_toLp ((dynkinProcess_memLp hP f t).sub (dynkinProcess_memLp hP f 0))
  have hrep : (∫ η, inner ℝ (dynkinIncrementLp hP f t η) (dynkinIncrementLp hP f t η) ∂P) =
      ∫ η, (dynkinProcess hP f t η - dynkinProcess hP f 0 η) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [hm] with η hη
    rw [hη]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  rw [hrep, integral_dynkin_increment_sq_eq_energy hP hcoord f t]

/-- The `L²` norm of the limiting resolvent martingale is determined by the correlation integral. -/
theorem norm_resolvent_martingale_limit_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (t : ℝ≥0) :
    ‖Z t‖ ^ 2 = (t : ℝ) * (2 * ∫ u in Set.Ioi (0 : ℝ),
      inner ℝ f (transitionOperator hP u.toNNReal f)) := by
  have hnorm := (hZ t).norm.pow 2
  have henergy := (tendsto_resolvent_generator_energy hP f hint).const_mul 2
  have hlimit := henergy.const_mul (t : ℝ)
  have heq : (fun n : ℕ => ‖dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t‖ ^ 2) =
      (fun n : ℕ => (t : ℝ) * (2 * -inner ℝ
        (transitionResolventDomain hP (reciprocalShift n) f : Lp ℝ 2 μ)
        ((transitionSemigroup hP).generator (transitionResolventDomain hP (reciprocalShift n) f)))) := by
    funext n
    exact norm_dynkinIncrementLp_sq hP hcoord _ t
  rw [heq] at hnorm
  exact tendsto_nhds_unique hnorm hlimit

end EinsteinFull.External.DFGW
