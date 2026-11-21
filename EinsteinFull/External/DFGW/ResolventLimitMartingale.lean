import EinsteinFull.External.DFGW.ResolventMartingaleLimit
import EinsteinFull.External.DFGW.DynkinCentered

/-! # Martingale property of the resolvent limit

The fixed-time `L²` limits of the centered Dynkin resolvent approximations admit strongly
adapted representatives forming a martingale.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Any fixed-time `L²` limit of the resolvent martingales satisfies the `L²` martingale
conditional expectation identity. -/
theorem condExpL2_resolvent_limit (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    {s t : ℝ≥0} (hst : s ≤ t) :
    (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le s) (Z t) : Lp ℝ 2 P) = Z s := by
  let : IsProbabilityMeasure P := hP.probability
  let C : Lp ℝ 2 P → Lp ℝ 2 P := fun x =>
    (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le s) x : Lp ℝ 2 P)
  have hcont : Continuous C :=
    continuous_subtype_val.comp (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le s)).continuous
  have hleft := (hcont.tendsto (Z t)).comp (hZ t)
  have heq : (fun n : ℕ => C (dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t)) =
      (fun n : ℕ => dynkinIncrementLp hP
        (transitionResolventDomain hP (reciprocalShift n) f) s) := by
    funext n
    exact condExpL2_dynkinIncrementLp hP hcoord _ hst
  change Tendsto (fun n : ℕ => C (dynkinIncrementLp hP
    (transitionResolventDomain hP (reciprocalShift n) f) t)) atTop (𝓝 (C (Z t))) at hleft
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (hZ s)

/-- Resolvent martingales have a strongly adapted martingale as their fixed-time `L²` limit. -/
theorem exists_martingale_resolvent_limit (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    ∃ (Z : ℝ≥0 → Lp ℝ 2 P) (M : ℝ≥0 → C(ℝ, S) → ℝ),
      (∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
        (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t))) ∧
      (∀ t, M t =ᵐ[P] Z t) ∧ Martingale M Draft.dfgwPast P := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨Z, hZ, _⟩ := existsUnique_resolvent_dynkinIncrement_family hP hcoord f hint
  let M : ℝ≥0 → C(ℝ, S) → ℝ := fun t => P[Z t | Draft.dfgwPast t]
  have hcond (s t : ℝ≥0) (hst : s ≤ t) : P[Z t | Draft.dfgwPast s] =ᵐ[P] Z s := by
    have hLp : (Lp.memLp (Z t)).toLp (Z t) = Z t := Lp.toLp_coeFn (Z t) _
    have hce : (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le s)
        ((Lp.memLp (Z t)).toLp (Z t)) : Lp ℝ 2 P) =ᵐ[P] P[Z t | Draft.dfgwPast s] :=
      (Lp.memLp (Z t)).condExpL2_ae_eq_condExp ((Draft.dfgwPast (S := S)).le s)
    rw [hLp, condExpL2_resolvent_limit hP hcoord f Z hZ hst] at hce
    exact hce.symm
  have hrep (t : ℝ≥0) : M t =ᵐ[P] Z t := hcond t t le_rfl
  refine ⟨Z, M, hZ, hrep, ?_⟩
  refine ⟨fun t => stronglyMeasurable_condExp, ?_⟩
  intro s t hst
  have heq := condExp_congr_ae (m := Draft.dfgwPast s) (hrep t)
  exact heq.trans ((hcond s t hst).trans (hrep s).symm)

end EinsteinFull.External.DFGW
