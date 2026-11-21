import EinsteinFull.External.DFGW.ResolventRemainderAllTimes
import EinsteinFull.External.DFGW.ResolventLimitMartingale

/-! # Martingale approximation of integrated observables

An integrated stationary observable with integrable autocorrelation admits a square-integrable
stationary-increment martingale approximation whose remainder has mean square `o(t)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Any fixed-time `L²` limit of the resolvent martingales, represented by a martingale, is
square integrable, has stationary increments and the limiting variance, and approximates the
integrated observable with a sublinear mean-square remainder. -/
theorem resolvent_limit_martingale_properties (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P) (M : ℝ≥0 → C(ℝ, S) → ℝ)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (hrep : ∀ t, M t =ᵐ[P] Z t) :
    (∀ t, MemLp (M t) 2 P) ∧
      (∀ s t, (fun η => M (s + t) η - M s η) =ᵐ[P]
        fun η => M t (Draft.dfgwShift s η)) ∧
      (∀ t, (∫ η, (M t η) ^ 2 ∂P) = (t : ℝ) * (2 *
        ∫ u in Set.Ioi (0 : ℝ), inner ℝ f (transitionOperator hP u.toNNReal f))) ∧
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        ∫ η, ((∫ u in (0 : ℝ)..t, f (η u)) - M t η) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  have hMLp (t : ℝ≥0) : MemLp (M t) 2 P := (memLp_congr_ae (hrep t)).2 (Lp.memLp (Z t))
  have hnorm (t : ℝ≥0) : (∫ η, (M t η) ^ 2 ∂P) = ‖Z t‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep t] with η hη
    rw [hη]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have hstationary (s t : ℝ≥0) : (fun η => M (s + t) η - M s η) =ᵐ[P]
      fun η => M t (Draft.dfgwShift s η) := by
    let hshift : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
      ⟨measurable_shift s, hP.stationary s⟩
    have hs := resolvent_limit_stationary_increments hP f Z hZ s t
    have hcomp := Lp.coeFn_compMeasurePreserving (Z t) hshift
    have hsub := Lp.coeFn_sub (Z (s + t)) (Z s)
    have hr := hshift.quasiMeasurePreserving.ae (hrep t)
    filter_upwards [hrep (s + t), hrep s, hr, hcomp, hsub] with η ha hb hc hd he
    simp only [Function.comp_apply, Pi.sub_apply] at hc hd he
    have hsη : (Z (s + t) - Z s) η = Lp.compMeasurePreserving _ hshift (Z t) η :=
      congrArg (fun F : Lp ℝ 2 P => F η) hs
    rw [he, hd] at hsη
    linarith
  have hrem (t : ℝ≥0) :
      (∫ η, ((∫ u in (0 : ℝ)..t, f (η u)) - M t η) ^ 2 ∂P) =
        ‖timeIntegralLp hP f t - Z t‖ ^ 2 := by
    have htime : timeIntegralLp hP f t =ᵐ[P]
        fun η => ∫ u in (0 : ℝ)..t, f (η u) :=
      MemLp.coeFn_toLp ((time_integral_memLp_and_sq_le hP f (Lp.memLp f) t.coe_nonneg).1)
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [htime, hrep t, Lp.coeFn_sub (timeIntegralLp hP f t) (Z t)] with η htη hmη hsη
    simp only [Pi.sub_apply] at hsη
    rw [hsη, htη, ← hmη]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  refine ⟨hMLp, hstationary, ?_, ?_⟩
  · intro t
    rw [hnorm, norm_resolvent_martingale_limit_sq hP hcoord f hint Z hZ t]
  · simpa only [hrem] using tendsto_resolvent_remainder_atTop hP hcoord f hint Z hZ

/-- A stationary integrated `L²` observable with integrable autocorrelation has a
stationary-increment martingale approximation with a sublinear mean-square remainder. -/
theorem exists_martingale_approximation (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    ∃ M : ℝ≥0 → C(ℝ, S) → ℝ,
      Martingale M Draft.dfgwPast P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ s t, (fun η => M (s + t) η - M s η) =ᵐ[P]
        fun η => M t (Draft.dfgwShift s η)) ∧
      (∀ t, (∫ η, (M t η) ^ 2 ∂P) = (t : ℝ) * (2 *
        ∫ u in Set.Ioi (0 : ℝ), inner ℝ f (transitionOperator hP u.toNNReal f))) ∧
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        ∫ η, ((∫ u in (0 : ℝ)..t, f (η u)) - M t η) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨Z, M, hZ, hrep, hM⟩ := exists_martingale_resolvent_limit hP hcoord f hint
  exact ⟨M, hM, resolvent_limit_martingale_properties hP hcoord f hint Z M hZ hrep⟩

end EinsteinFull.External.DFGW
