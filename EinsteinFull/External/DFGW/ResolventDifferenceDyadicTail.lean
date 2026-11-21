import EinsteinFull.External.DFGW.ResolventDyadicMaximalBound

/-! # Dyadic tails of resolvent differences

Cauchy convergence in Dirichlet energy and vanishing normalized resolvent norms make the
maximal difference between a varying and a sufficiently small fixed resolvent negligible.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A sufficiently small fixed resolvent approximates varying resolvents uniformly on long
dyadic intervals at diffusive scale. -/
theorem eventually_small_resolvent_difference_dyadic_max
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (θ : ℝ) (hθ : 0 < θ) :
    ∀ ρ > 0, ∃ m : ℕ, ∀ᶠ n : ℕ in atTop,
      let F := transitionResolventDomain hP (reciprocalShift n) f -
        transitionResolventDomain hP (reciprocalShift m) f
      P.real {η | ∃ r k, k ≤ 2 ^ r ∧ θ * Real.sqrt (n + 1) ≤
        |(F : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))|} < ρ := by
  intro ρ hρ
  let τ : ℝ := θ * ρ / 16
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  obtain ⟨N, hN⟩ := resolvent_energy_cauchy hP f hint (τ ^ 2 / 2) (by positivity)
  refine ⟨N, ?_⟩
  have hnorm := tendsto_normalized_resolvent_difference_norm hP f hint N
  have hsmall : ∀ᶠ n : ℕ in atTop, (Real.sqrt (n + 1))⁻¹ *
      ‖transitionResolvent hP (reciprocalShift n) f -
        transitionResolvent hP (reciprocalShift N) f‖ < θ * ρ / 8 :=
    hnorm.eventually (gt_mem_nhds (by positivity))
  filter_upwards [eventually_ge_atTop N, hsmall] with n hn hnormn
  let F := transitionResolventDomain hP (reciprocalShift n) f -
    transitionResolventDomain hP (reciprocalShift N) f
  have he : -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F) < τ ^ 2 / 2 :=
    hN n hn N le_rfl
  have he0 : 0 ≤ -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F) :=
    (transitionResolvent_difference_energy_bounds hP (reciprocalShift n) (reciprocalShift N) f).1
  have hsqrt : Real.sqrt (2 * -inner ℝ (F : Lp ℝ 2 μ)
      ((transitionSemigroup hP).generator F)) < τ := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * -inner ℝ (F : Lp ℝ 2 μ)
      ((transitionSemigroup hP).generator F) by positivity)
    have hnonsqrt := Real.sqrt_nonneg (2 * -inner ℝ (F : Lp ℝ 2 μ)
      ((transitionSemigroup hP).generator F))
    nlinarith
  have hbound := measureReal_max_resolvent_difference_le hP hcoord f n N θ hθ
  have hnormF : (Real.sqrt (n + 1))⁻¹ * ‖(F : Lp ℝ 2 μ)‖ < θ * ρ / 8 := hnormn
  dsimp only [F] at hbound hnormF hsqrt
  dsimp only [F]
  dsimp only [τ] at hsqrt
  nlinarith

end EinsteinFull.External.DFGW
