import EinsteinFull.External.DFGW.ResolventDyadicRepresentatives
import EinsteinFull.External.DFGW.LongDyadicObservableTail

/-! # Dyadic maximal tails of varying resolvents

The energy approximation by a fixed resolvent and the fixed-resolvent block tail imply that
reciprocal resolvents are uniformly negligible on long dyadic intervals at diffusive scale.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Reciprocal resolvents are uniformly negligible on long dyadic grids at diffusive scale. -/
theorem tendsto_measureReal_max_reciprocal_resolvent_dyadic
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun n : ℕ => P.real {η | ∃ r k, k ≤ 2 ^ r ∧
      θ * Real.sqrt (n + 1) ≤ |transitionResolvent hP (reciprocalShift n) f
        (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))|}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  apply Metric.tendsto_nhds.mpr
  intro ρ hρ
  obtain ⟨m, hvar⟩ := eventually_small_resolvent_difference_dyadic_max hP hcoord f hint
    (θ / 2) (by positivity) (ρ / 2) (by positivity)
  let G := transitionResolventDomain hP (reciprocalShift m) f
  have hfixed := (tendsto_measureReal_max_dyadic_observable_long_interval hP hcoord G
    (δ := (θ / 2) ^ 2) (by positivity)).comp (tendsto_add_atTop_nat 1)
  have hfixedsmall := hfixed.eventually (gt_mem_nhds (show 0 < ρ / 2 by positivity))
  filter_upwards [hvar, hfixedsmall] with n hvarn hfixn
  let F := transitionResolventDomain hP (reciprocalShift n) f - G
  let A : Set C(ℝ, S) := {η | ∃ r k, k ≤ 2 ^ r ∧
    θ * Real.sqrt (n + 1) ≤ |transitionResolvent hP (reciprocalShift n) f
      (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))|}
  let B : Set C(ℝ, S) := {η | ∃ r k, k ≤ 2 ^ r ∧
    (θ / 2) * Real.sqrt (n + 1) ≤ |(F : Lp ℝ 2 μ)
      (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))|}
  let C : Set C(ℝ, S) := {η | ∃ r k, k ≤ 2 ^ r ∧
    (θ / 2) ^ 2 * (n + 1 : ℕ) ≤ |(G : Lp ℝ 2 μ)
      (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))| ^ 2}
  have hsub : A ≤ᵐ[P] B ∪ C := by
    filter_upwards [ae_resolvent_difference_dyadic hP f m] with η hη hA
    by_contra hnot
    obtain ⟨r, k, hk, hlarge⟩ := hA
    have hB : |(F : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))| <
        (θ / 2) * Real.sqrt (n + 1) := by
      apply lt_of_not_ge
      intro h
      exact hnot (Or.inl ⟨r, k, hk, h⟩)
    have hC : |(G : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))| ^ 2 <
        (θ / 2) ^ 2 * (n + 1 : ℕ) := by
      apply lt_of_not_ge
      intro h
      exact hnot (Or.inr ⟨r, k, hk, h⟩)
    have hroot : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hroot2 : (Real.sqrt (n + 1 : ℝ)) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
    have hhalf : 0 < (θ / 2) * Real.sqrt (n + 1) := by positivity
    have hG : |(G : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k))| <
        (θ / 2) * Real.sqrt (n + 1) := by
      have hscale : ((θ / 2) * Real.sqrt (n + 1)) ^ 2 =
          (θ / 2) ^ 2 * ((n + 1 : ℕ) : ℝ) := by
        rw [mul_pow, hroot2]
        push_cast
        rfl
      nlinarith [abs_nonneg ((G : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)))]
    have hrepr := hη n r k
    change (F : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) = _ at hrepr
    have htri := abs_add_le
      ((F : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)))
      ((G : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)))
    have heq : (F : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) +
        (G : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) =
        transitionResolvent hP (reciprocalShift n) f
          (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) := by
      change (F : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) =
        transitionResolvent hP (reciprocalShift n) f
          (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) -
        (G : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) at hrepr
      linarith
    rw [heq] at htri
    linarith
  have hbound : P.real A ≤ P.real B + P.real C := by
    exact (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans
      (measureReal_union_le _ _)
  have hBsmall : P.real B < ρ / 2 := hvarn
  have hCsmall : P.real C < ρ / 2 := hfixn
  change dist (P.real A) 0 < ρ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

end EinsteinFull.External.DFGW
