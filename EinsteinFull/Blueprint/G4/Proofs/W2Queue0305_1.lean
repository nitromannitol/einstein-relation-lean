import EinsteinFull.Blueprint.G4.node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removal
import EinsteinFull.Blueprint.Roots.node_p_u3A_tail
import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_actual_u2D_kernel_u2D_application
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma integrable_of_exponential_tail {f : ℝ → ℂ} (hf : Continuous f)
    {A b T : ℝ} (hb : 0 < b)
    (htail : ∀ t : ℝ, T ≤ t → ‖f t‖ ≤ A * Real.exp (-b * t)) :
    IntegrableOn f (Set.Ioi 0) := by
  have hn : IntegrableOn (fun t => ‖f t‖) (Set.Ioi 0) := by
    apply integrable_of_isBigO_exp_neg hb hf.norm.continuousOn
    refine Asymptotics.IsBigO.of_bound A ?_
    filter_upwards [eventually_ge_atTop T] with t ht
    simpa only [Real.norm_eq_abs, abs_norm, abs_of_pos (Real.exp_pos _)] using htail t ht
  exact (integrable_norm_iff hf.aestronglyMeasurable).mp hn

private lemma abel_limit {f : ℝ → ℂ} (hf : IntegrableOn f (Set.Ioi 0)) :
    Tendsto (fun s : ℝ => ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-s * t) : ℂ) * f t) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), f t)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖)
  · exact Eventually.of_forall fun s =>
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hs)) (le_of_lt ht)))
  · exact hf.norm
  · exact ae_of_all _ fun t => by
      have he : Tendsto (fun s : ℝ => (Real.exp (-s * t) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
        have he' : Continuous (fun s : ℝ => (Real.exp (-s * t) : ℂ)) :=
          Complex.continuous_ofReal.comp
            (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const))
        simpa only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one] using
          (he'.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa only [one_mul] using he.mul_const (f t)

private lemma continuous_pair_orbit {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (b f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : ℝ => ∫ ω, b ω * (P t.toNNReal f) ω ∂reducedLaw Q) := by
  let L := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 b
  have hc := L.continuous.comp ((hP.2.2.1 f).comp continuous_real_toNNReal)
  simpa only [Function.comp_def, L, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply'] using hc

/-- Time continuity and the exponential tail give absolute convergence, then
Lebesgue dominated convergence removes the Abel damping at each signed force. -/
@[nolint unusedArguments]
theorem node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removal_of_deps
    (_hresponse : node_p_u3A_responseStmt)
    (htail : node_p_u3A_tailStmt)
    (_hkernel : node_p_u3A_integration_u23_actual_u2D_kernel_u2D_applicationStmt) :
    node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removalStmt := by
  intro d hd D
  obtain ⟨C, c, CT, _hC, hc, _hCT, htail⟩ := htail d hd D
  refine ⟨Real.exp (-1), Real.exp_pos _, ?_⟩
  intro Q hQ β a μ hβ ha hμ P hP lam hlam hsmall
  dsimp only
  let first : Fin d := ⟨0, by omega⟩
  have hb : 0 < c * lam ^ 2 := mul_pos hc (sq_pos_of_ne_zero hlam)
  have hbound := htail Q hQ β a μ hβ ha hμ lam (abs_pos.mpr hlam) hsmall
    (P (lam : ℂ)) (hP (lam : ℂ))
  have hv (i : Fin d) : IntegrableOn
      (fun t : ℝ => velocityCorrelation Q first i (lam : ℂ) (P (lam : ℂ)) β a t.toNNReal)
      (Set.Ioi 0) := by
    apply integrable_of_exponential_tail
      (continuous_pair_orbit Q (hP (lam : ℂ)) (β first) (β i + (lam : ℂ) • a first i)) hb
      (A := C * |lam| ^ (d + 2) * Real.exp (C * Real.sqrt (Real.log (1 / |lam|))))
      (T := max 0 (CT / |lam| ^ 2))
    intro t ht
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
    have h := (hbound t.toNNReal (by simpa only [Real.coe_toNNReal t ht0] using
      (le_max_right 0 (CT / |lam| ^ 2)).trans ht) i).1
    rw [Real.coe_toNNReal t ht0, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg] at h
    simpa only [mul_assoc, neg_mul] using! h
  have hj : IntegrableOn
      (fun t : ℝ => clockCorrelation Q first (lam : ℂ) (P (lam : ℂ)) β μ t.toNNReal)
      (Set.Ioi 0) := by
    apply integrable_of_exponential_tail
      (continuous_pair_orbit Q (hP (lam : ℂ)) (β first) ((lam : ℂ) • μ)) hb
      (A := C * |lam| ^ (d + 2) * Real.exp (C * Real.sqrt (Real.log (1 / |lam|))))
      (T := max 0 (CT / |lam| ^ 2))
    intro t ht
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
    have h := (hbound t.toNNReal (by simpa only [Real.coe_toNNReal t ht0] using
      (le_max_right 0 (CT / |lam| ^ 2)).trans ht) first).2
    rw [Real.coe_toNNReal t ht0, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg] at h
    simpa only [mul_assoc, neg_mul] using! h
  exact ⟨fun i => ⟨hv i, abel_limit (hv i)⟩, hj, abel_limit hj⟩

end EinsteinFull.Blueprint
