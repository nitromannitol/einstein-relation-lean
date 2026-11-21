import EinsteinFull.External.DFGW.DynkinExpectation
import EinsteinFull.External.DFGW.PastTimeIntegral
import EinsteinFull.External.DFGW.TimeIntegralBound

/-! # Square-integrable Dynkin martingales

A generator-domain observable of a stationary Markov process, compensated by the time
integral of its generator, is a square-integrable martingale.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A generator-domain observable compensated by its integrated generator. -/
noncomputable def dynkinProcess (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) (η : C(ℝ, S)) : ℝ :=
  (f : Lp ℝ 2 μ) (η t) - ∫ u in (0 : ℝ)..t, (transitionSemigroup hP).generator f (η u)

/-- The compensated generator-domain observable is square-integrable at every time. -/
theorem dynkinProcess_memLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    MemLp (dynkinProcess hP f t) 2 P := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have hev : MeasurePreserving (fun η : C(ℝ, S) => η (t : ℝ)) P μ :=
    ⟨(continuous_eval_const _).measurable, hP.marginal _⟩
  have hval := (Lp.memLp (f : Lp ℝ 2 μ)).comp_measurePreserving hev
  have hint := (time_integral_memLp_and_sq_le hP _
    (Lp.memLp ((transitionSemigroup hP).generator f)) t.coe_nonneg).1
  exact hval.sub hint

/-- The compensated generator-domain observable is strongly adapted to the past. -/
theorem stronglyAdapted_dynkinProcess (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) :
    StronglyAdapted Draft.dfgwPast (dynkinProcess hP f) := by
  intro t
  have heval : Measurable[Draft.dfgwCoordSigma (Set.Iic (t : ℝ))]
      (fun η : C(ℝ, S) => η (t : ℝ)) := by
    apply Measurable.of_comap_le
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic (t : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance)
        (t : ℝ) (by change (t : ℝ) ≤ t; exact le_rfl) le_rfl
  have hf : StronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic (t : ℝ))]
      (fun η : C(ℝ, S) => (f : Lp ℝ 2 μ) (η t)) :=
    (Lp.stronglyMeasurable (f : Lp ℝ 2 μ)).comp_measurable heval
  exact hf.sub (stronglyMeasurable_time_integral_past hcoord _
    (Lp.stronglyMeasurable ((transitionSemigroup hP).generator f)).measurable t)

/-- The square-integrable Dynkin process is a martingale for the past filtration. -/
theorem martingale_dynkinProcess (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) :
    Martingale (dynkinProcess hP f) Draft.dfgwPast P := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  refine ⟨stronglyAdapted_dynkinProcess hP hcoord f, ?_⟩
  intro s t hst
  let u : ℝ≥0 := t - s
  let g := (transitionSemigroup hP).generator f
  let A : C(ℝ, S) → ℝ := fun η => (f : Lp ℝ 2 μ) (η ((u : ℝ) + s)) -
    ∫ v in (0 : ℝ)..u, g (η (v + s))
  let B : C(ℝ, S) → ℝ := fun η => ∫ v in (0 : ℝ)..s, g (η v)
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hut : (u : ℝ) + s = t := by simp only [u, NNReal.coe_sub hst]; ring
  have hB : Integrable B P :=
    (integral_time_observable hP g ((Lp.memLp g).integrable one_le_two) s.coe_nonneg).1
  have hBmeas : StronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] B :=
    stronglyMeasurable_time_integral_past hcoord g (Lp.stronglyMeasurable g).measurable s
  have hev : MeasurePreserving (fun η : C(ℝ, S) => η ((u : ℝ) + s)) P μ :=
    ⟨(continuous_eval_const _).measurable, hP.marginal _⟩
  have hval : Integrable (fun η : C(ℝ, S) => (f : Lp ℝ 2 μ) (η ((u : ℝ) + s))) P :=
    ((Lp.memLp (f : Lp ℝ 2 μ)).comp_measurePreserving hev).integrable one_le_two
  have hshift : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
    ⟨measurable_shift s, hP.stationary s⟩
  have hshiftint : Integrable (fun η : C(ℝ, S) => ∫ v in (0 : ℝ)..u, g (η (v + s))) P := by
    have h := hshift.integrable_comp_of_integrable
      (integral_time_observable hP g ((Lp.memLp g).integrable one_le_two) u.coe_nonneg).1
    simpa only [Function.comp_def, Draft.dfgwShift, ContinuousMap.coe_comp,
      ContinuousMap.coe_mk] using h
  have hA : Integrable A P := hval.sub hshiftint
  have hpath : ∀ᵐ η ∂P, IntervalIntegrable (fun v => g (η v)) volume 0 s ∧
      IntervalIntegrable (fun v => g (η v)) volume s t := by
    have h1 := (integrable_joint_observable hP g ((Lp.memLp g).integrable one_le_two) 0 s).prod_left_ae
    have h2 := (integrable_joint_observable hP g ((Lp.memLp g).integrable one_le_two) s t).prod_left_ae
    filter_upwards [h1, h2] with η h1η h2η
    exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg).2 h1η,
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst').2 h2η⟩
  have hdecomp : dynkinProcess hP f t =ᵐ[P] A - B := by
    filter_upwards [hpath] with η hη
    have hsum := intervalIntegral.integral_add_adjacent_intervals hη.1 hη.2
    have hshiftEq : (∫ v in (0 : ℝ)..u, g (η (v + s))) = ∫ v in (s : ℝ)..t, g (η v) := by
      simpa only [zero_add, hut] using
        (intervalIntegral.integral_comp_add_right (fun v => g (η v)) (a := 0) (b := u) s)
    change (f : Lp ℝ 2 μ) (η t) - (∫ v in (0 : ℝ)..t, g (η v)) = A η - B η
    dsimp only [A, B]
    rw [hut, hshiftEq, ← hsum]
    ring
  have hc := condExp_congr_ae (m := Draft.dfgwCoordSigma (Set.Iic (s : ℝ))) hdecomp
  have hsub := condExp_sub hA hB (Draft.dfgwCoordSigma (Set.Iic (s : ℝ)))
  have hknown := condExp_dynkin_shift hP s u f
  have hBcond := condExp_of_stronglyMeasurable ((Draft.dfgwPast (S := S)).le s) hBmeas hB
  change P[B | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] = B at hBcond
  filter_upwards [hc, hsub, hknown] with η hcη hsη hkη
  change P[dynkinProcess hP f t | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] η = dynkinProcess hP f s η
  rw [hcη, hsη, Pi.sub_apply, hBcond]
  change P[A | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] η - B η = _
  rw [hkη]
  rfl

end EinsteinFull.External.DFGW
