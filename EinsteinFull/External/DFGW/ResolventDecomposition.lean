import EinsteinFull.External.DFGW.ResolventLimitStationary
import EinsteinFull.External.DFGW.TimeIntegralLinearity

/-! # Resolvent decomposition of additive functionals

The time integral of a state observable decomposes into a Dynkin martingale increment, a
resolvent boundary term, and a normalized resolvent time integral.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Evaluation of an `L²` state observable at a fixed stationary trajectory time. -/
noncomputable def stateEvaluationLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (t : ℝ≥0) : Lp ℝ 2 P :=
  Lp.compMeasurePreserving (fun η : C(ℝ, S) => η (t : ℝ))
    ⟨(continuous_eval_const _).measurable, hP.marginal _⟩ f

/-- The `L²` norm of a stationary evaluation is the state-space `L²` norm. -/
theorem norm_stateEvaluationLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (t : ℝ≥0) : ‖stateEvaluationLp hP f t‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f _

/-- A centered Dynkin increment is its boundary increment minus the integrated generator. -/
theorem dynkinIncrementLp_eq_boundary_sub (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    dynkinIncrementLp hP f t = stateEvaluationLp hP f t - stateEvaluationLp hP f 0 -
      timeIntegralLp hP ((transitionSemigroup hP).generator f) t := by
  let F : Lp ℝ 2 μ := f
  let G := (transitionSemigroup hP).generator f
  have hrepr : dynkinIncrementLp hP f t =ᵐ[P]
      fun η => dynkinProcess hP f t η - dynkinProcess hP f 0 η :=
    MemLp.coeFn_toLp ((dynkinProcess_memLp hP f t).sub (dynkinProcess_memLp hP f 0))
  have hev (u : ℝ≥0) : stateEvaluationLp hP F u =ᵐ[P]
      fun η => F (η u) := Lp.coeFn_compMeasurePreserving F _
  have hint : timeIntegralLp hP G t =ᵐ[P] fun η => ∫ u in (0 : ℝ)..t, G (η u) :=
    MemLp.coeFn_toLp ((time_integral_memLp_and_sq_le hP G (Lp.memLp G) t.coe_nonneg).1)
  have hsub1 := Lp.coeFn_sub (stateEvaluationLp hP F t) (stateEvaluationLp hP F 0)
  have hsub2 := Lp.coeFn_sub (stateEvaluationLp hP F t - stateEvaluationLp hP F 0)
    (timeIntegralLp hP G t)
  apply Lp.ext
  filter_upwards [hrepr, hev t, hev 0, hint, hsub1, hsub2] with η hr hvt hv0 hi hs1 hs2
  simp only [Pi.sub_apply, Function.comp_apply] at hs1 hs2 hvt hv0
  rw [hr, hs2, hs1, hvt, hv0, hi]
  simp only [dynkinProcess, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero, F, G]
  ring

/-- Exact `L²` resolvent decomposition of an integrated state observable. -/
theorem timeIntegralLp_sub_resolvent_martingale (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (a : MarkovProcess.Semigroup.PositiveShift) (t : ℝ≥0) :
    timeIntegralLp hP f t - dynkinIncrementLp hP (transitionResolventDomain hP a f) t =
      -(stateEvaluationLp hP (transitionResolvent hP a f) t -
        stateEvaluationLp hP (transitionResolvent hP a f) 0) +
      (a : ℝ) • timeIntegralLp hP (transitionResolvent hP a f) t := by
  let F := transitionResolventDomain hP a f
  have hgen : (transitionSemigroup hP).generator F = (a : ℝ) • transitionResolvent hP a f - f := by
    dsimp only [F, transitionResolventDomain, transitionResolvent]
    exact (transitionSemigroup hP).generator_resolvent a f
  have hdyn := dynkinIncrementLp_eq_boundary_sub hP F t
  rw [hgen, timeIntegralLp_sub, timeIntegralLp_smul] at hdyn
  change dynkinIncrementLp hP F t =
    stateEvaluationLp hP (transitionResolvent hP a f) t -
      stateEvaluationLp hP (transitionResolvent hP a f) 0 -
      ((a : ℝ) • timeIntegralLp hP (transitionResolvent hP a f) t - timeIntegralLp hP f t) at hdyn
  change timeIntegralLp hP f t - dynkinIncrementLp hP F t = _
  rw [hdyn]
  abel

/-- The resolvent approximation error is bounded by a boundary term and an integrated
normalized resolvent. -/
theorem norm_timeIntegralLp_sub_resolvent_martingale_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (a : MarkovProcess.Semigroup.PositiveShift) (t : ℝ≥0) :
    ‖timeIntegralLp hP f t - dynkinIncrementLp hP (transitionResolventDomain hP a f) t‖ ≤
      (2 + (a : ℝ) * (t : ℝ)) * ‖transitionResolvent hP a f‖ := by
  rw [timeIntegralLp_sub_resolvent_martingale]
  have hb := norm_sub_le (stateEvaluationLp hP (transitionResolvent hP a f) t)
    (stateEvaluationLp hP (transitionResolvent hP a f) 0)
  rw [norm_stateEvaluationLp, norm_stateEvaluationLp] at hb
  have hi := norm_timeIntegralLp_le hP (transitionResolvent hP a f) t
  have ha : 0 ≤ (a : ℝ) := a.2.le
  calc
    _ ≤ ‖-(stateEvaluationLp hP (transitionResolvent hP a f) t -
        stateEvaluationLp hP (transitionResolvent hP a f) 0)‖ +
        ‖(a : ℝ) • timeIntegralLp hP (transitionResolvent hP a f) t‖ := norm_add_le _ _
    _ ≤ (‖transitionResolvent hP a f‖ + ‖transitionResolvent hP a f‖) +
        (a : ℝ) * ((t : ℝ) * ‖transitionResolvent hP a f‖) := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      gcongr
    _ = _ := by ring

end EinsteinFull.External.DFGW
