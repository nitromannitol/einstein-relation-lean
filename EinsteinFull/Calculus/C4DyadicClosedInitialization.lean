import EinsteinFull.Calculus.C4DyadicFiniteForceInitialization
import EinsteinFull.Calculus.C19FirstUnitGradientProjection
import EinsteinFull.Calculus.ComplexHighExponentAnalyticSupport
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Cauchy estimates supply an integrable Lipschitz majorant on a finite time window. -/
private theorem analytic_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (F : ℂ → ℝ → E) (T : ℝ)
    (hc : ∀ z, Continuous (F z)) (ha : ∀ r, Differentiable ℂ (fun z => F z r))
    (hb : ∀ z, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall z 2,
      ∀ r ∈ Icc 0 T, ‖F w r‖ ≤ C) (z : ℂ) :
    AnalyticAt ℂ (fun w => ∫ r in Icc 0 T, F w r) z := by
  apply Differentiable.analyticAt (f := fun w => ∫ r in Icc 0 T, F w r) _ z
  intro z₀
  obtain ⟨C, hC, hbound⟩ := hb z₀
  have hm : ∀ w, AEStronglyMeasurable (F w) (volume.restrict (Icc 0 T)) :=
    fun w => (hc w).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (fun r => deriv (fun w => F w r) z₀)
      (volume.restrict (Icc 0 T)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) r => (1 / ((n : ℂ) + 1))⁻¹ •
        (F (z₀ + 1 / ((n : ℂ) + 1)) r - F z₀ r))
    · intro n
      exact ((hm _).sub (hm _)).const_smul _
    · apply Eventually.of_forall
      intro r
      apply ((ha r z₀).hasDerivAt.tendsto_slope_zero).comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ?_⟩
      intro n
      change 1 / ((n : ℂ) + 1) ≠ 0
      exact one_div_ne_zero (by exact_mod_cast (Nat.succ_ne_zero n))
  have hd : ∀ r ∈ Icc 0 T, ∀ w ∈ Metric.ball z₀ 1,
      ‖deriv (fun u => F u r) w‖ ≤ C := by
    intro r hr w hw
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (c := w) (C := C) (by norm_num : (0 : ℝ) < 1) (ha r).diffContOnCl
      (fun u hu => hbound u (Metric.mem_closedBall.mpr ?_) r hr)
    · simpa only [div_one] using! h
    · have hdist := dist_triangle u w z₀
      have hwu := Metric.mem_sphere.mp hu
      have hw₀ := Metric.mem_ball.mp hw
      linarith
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (μ := volume.restrict (Icc 0 T)) (bound := fun _ => C)
    (Metric.ball_mem_nhds z₀ zero_lt_one) (Eventually.of_forall hm)
    ((hc z₀).continuousOn.integrableOn_Icc) hdmeas
    ?_ (integrable_const C) (Eventually.of_forall fun r => (ha r z₀).hasDerivAt)
  · exact hdiff.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun w _ => ha r w) ?_ (convex_ball z₀ 1)
    intro w hw
    exact_mod_cast (show ‖deriv (fun u => F u r) w‖ ≤ |C| by
      rw [abs_of_nonneg hC]; exact hd r hr w hw)

/-- Integrating an entire strongly continuous family preserves force holomorphy. -/
private theorem analytic_orbit_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (F : ℂ → ℝ≥0 → E →L[ℂ] E)
    (hc : ∀ z f, Continuous (fun t => F z t f))
    (ha : ∀ t z, AnalyticAt ℂ (fun w => F w t) z)
    (a : ℂ → ℝ) (hac : Continuous a)
    (hn : ∀ z t, ‖F z t‖ ≤ Real.exp (a z * (t : ℝ)))
    (T : ℝ) (f : E) (z : ℂ) :
    AnalyticAt ℂ (fun w => ∫ r in Icc 0 T, F w r.toNNReal f) z := by
  apply analytic_integral _ T (fun w => (hc w f).comp continuous_real_toNNReal)
    (fun r w => (((ContinuousLinearMap.apply ℂ E f).analyticAt _).comp (ha r.toNNReal w)).differentiableAt)
    ?_ z
  intro w₀
  obtain ⟨M, hM⟩ := (isCompact_closedBall w₀ 2).bddAbove_image hac.continuousOn
  refine ⟨Real.exp (max M 0 * max T 0) * ‖f‖, by positivity, ?_⟩
  intro w hw r hr
  apply ((F w r.toNNReal).le_opNorm f).trans
  apply mul_le_mul_of_nonneg_right ((hn w r.toNNReal).trans ?_) (norm_nonneg f)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul ((hM ⟨w, hw, rfl⟩).trans (le_max_left M 0)) ?_
    (NNReal.coe_nonneg _) (le_max_right M 0)
  simpa only [Real.coe_toNNReal _ hr.1] using! hr.2.trans (le_max_left T 0)

private theorem c4_actual_analytic_semigroup :
    node_stationary_u2D_analytic_u2D_semigroupStmt := by
  intro d hd D
  constructor
  · intro Q _hQ
    dsimp only
    let i : Fin d := ⟨0, by omega⟩
    have hF := fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z
    have hG := fun z => isComplexTransposeSemigroup_complexL2Transpose Q
      (forcedComplexEvolution Q i z)
    refine ⟨fun z => ⟨hF z, hG z⟩, ?_, ?_⟩
    · exact fun t z => ⟨analyticAt_forcedComplexEvolution t z,
        analyticAt_forcedComplexEvolution_transpose t z⟩
    · intro t f z
      constructor
      · apply analytic_orbit_integral (forcedComplexEvolution Q i)
          (continuous_forcedComplexEvolution_apply Q i)
          (fun t z => analyticAt_forcedComplexEvolution t z)
          (complexForceShift d D.ellipticity) ?_
          (norm_forcedComplexEvolution_le Q i) (t : ℝ) f z
        unfold complexForceShift
        fun_prop
      · apply analytic_orbit_integral
          (fun z t => complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q i z t))
          (fun z f => (hG z).continuous_apply (hF z) f)
          (fun t z => analyticAt_forcedComplexEvolution_transpose t z)
          (complexForceShift d D.ellipticity) ?_
          (fun z t => (hG z).norm_le (hF z) t) (t : ℝ) f z
        unfold complexForceShift
        fun_prop
  · intro p R T hp hR hT
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    let K := Real.exp (2 * D.ellipticity) * D.ellipticity
    have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
      (zero_le_one.trans D.one_le_ellipticity)
    let C := Real.exp (((d : ℝ) * K * (R * K * (p - 1)) ^ 2) * T)
    refine ⟨C, Real.exp_pos _, ?_⟩
    intro Q _hQ
    dsimp only
    letI := reducedLaw_probability Q
    let i : Fin d := ⟨0, by omega⟩
    have hF := fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z
    have hG := fun z => isComplexTransposeSemigroup_complexL2Transpose Q
      (forcedComplexEvolution Q i z)
    intro f hf t ht
    have hp' : 2 ≤ ENNReal.ofReal p := by exact_mod_cast (ENNReal.ofReal_le_ofReal hp)
    have he : complexLpToL2 (reducedLaw Q) hp' (hf.toLp f) = f := by
      apply Lp.ext
      exact hf.coeFn_toLp
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨hm, hb⟩ := (hF z).highLp_bound hp f hf t
      obtain ⟨hmd, hbd⟩ := (hG z).highLp_bound (hF z) hp f hf t
      have hp1 : 0 ≤ p - 1 := by linarith
      have hforward : ‖z‖ * K ≤ R * K * (p - 1) := by
        calc
          _ ≤ R * K := mul_le_mul_of_nonneg_right hz hK
          _ ≤ R * K * (p - 1) := le_mul_of_one_le_right
            (mul_nonneg hR.le hK) (by linarith)
      have hbf : Real.exp (((d : ℝ) * K * (‖z‖ * K) ^ 2) * (t : ℝ)) ≤ C := by
        apply Real.exp_le_exp.mpr
        gcongr
      have hbt : Real.exp (((d : ℝ) * K * (‖z‖ * K * (p - 1)) ^ 2) * (t : ℝ)) ≤ C := by
        apply Real.exp_le_exp.mpr
        gcongr
      refine ⟨hm, hmd, ?_, ?_⟩
      · exact (hb.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hbf) _)).trans_eq
          (mul_comm _ _)
      · exact (hbd.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hbt) _)).trans_eq
          (mul_comm _ _)
    · refine ⟨fun z => (hF z).lpRestriction hp t (hf.toLp f),
        fun z => (hG z).lpRestriction hp (hF z) t (hf.toLp f), ?_, ?_⟩
      · intro z
        constructor
        · have h := (hF z).lpRestriction_apply hp t (hf.toLp f)
          rw [he] at h
          exact Lp.ext_iff.mp h
        · have h := (hG z).lpRestriction_apply hp (hF z) t (hf.toLp f)
          rw [he] at h
          exact Lp.ext_iff.mp h
      · exact fun z => ⟨analyticAt_complexEnvironmentSemigroup_lpRestriction_apply
          hp hF t (hf.toLp f) z,
          analyticAt_complexTransposeSemigroup_lpRestriction_apply hp hF hG t (hf.toLp f) z⟩


theorem c4_dyadic_bounded_time_initial_average_of_forced_local (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ s : ℝ, ∀ hs : 0 < s, ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ C * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4)) := by
  have hloc := c19_dyadic_locality_input_of_forced_local hlocal
  exact c4_dyadic_bounded_time_initial_average hloc
    (node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints_of_deps
      c4_actual_analytic_semigroup hloc) d hd D T hT

end EinsteinFull.Blueprint
