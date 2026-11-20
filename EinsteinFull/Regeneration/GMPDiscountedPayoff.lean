import EinsteinFull.Regeneration.GMPBoundedSlabPayoff
import EinsteinFull.Regeneration.ExitPayoffDiscount

/-!
# Zero-discount limit for GMP slab payoffs

Finite exit from the source slab implies finite exit from each bounded
subdomain. The discounted smooth payoff therefore converges to the actual
bounded-slab payoff without an exit-time moment assumption.
-/

open Filter MeasureTheory ProbabilityTheory Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The discounted finite-exit expectation of the smooth slab payoff. -/
noncomputable def gmpDiscountedSlabPayoff
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (y : Vec d) (N a : ℝ) (z : Vec d) : ℝ :=
  ∫ γ, {γ | MarkovProcess.ContinuousPath.exitTime (coordinateSlab i c R ∩ Metric.ball y N) γ < ⊤}.indicator
    (fun γ => Real.exp (-(a * (MarkovProcess.ContinuousPath.exitTime
      (coordinateSlab i c R ∩ Metric.ball y N) γ).toReal)) *
      slabSmoothPayoff i c R (γ ((MarkovProcess.ContinuousPath.exitTimeTop
        (coordinateSlab i c R ∩ Metric.ball y N) γ).untopD 0))) γ ∂G.pathLaw z

/-- Discounted slab payoffs are measurable in the starting point. -/
theorem measurable_gmpDiscountedSlabPayoff
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (y : Vec d) (N a : ℝ) :
    Measurable (gmpDiscountedSlabPayoff G i c R y N a) := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let U := coordinateSlab i c R ∩ Metric.ball y N
  have hU : IsOpen U := (isOpen_coordinateSlab i c R).inter Metric.isOpen_ball
  have hτ : Measurable (fun γ : Path d => (MarkovProcess.ContinuousPath.exitTime U γ).toReal) :=
    ENNReal.measurable_toReal.comp (MarkovProcess.ContinuousPath.measurable_exitTime U hU)
  have hF : Measurable (fun γ : Path d => slabSmoothPayoff i c R
      (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) :=
    (slabSmoothPayoff_smooth i c R).continuous.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop U hU)
  have hE := MarkovProcess.ContinuousPath.measurableSet_exitTime_lt_top U hU
  have hm : Measurable ({γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
      (fun γ => Real.exp (-(a * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
        slabSmoothPayoff i c R (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)))) :=
    ((Real.measurable_exp.comp ((measurable_const.mul hτ).neg)).mul hF).indicator hE
  exact hm.stronglyMeasurable.integral_kernel.measurable

/-- A nonnegative discount preserves the payoff's unit bounds. -/
theorem gmpDiscountedSlabPayoff_mem_Icc
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (y : Vec d) (N a : ℝ) (ha : 0 ≤ a) (z : Vec d) :
    gmpDiscountedSlabPayoff G i c R y N a z ∈ Set.Icc (0 : ℝ) 1 := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let U := coordinateSlab i c R ∩ Metric.ball y N
  let E : Set (Path d) := {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}
  let F : Path d → ℝ := fun γ => E.indicator
    (fun γ => Real.exp (-(a * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
      slabSmoothPayoff i c R (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ
  have hU : IsOpen U := (isOpen_coordinateSlab i c R).inter Metric.isOpen_ball
  have hτ : Measurable (fun γ : Path d => (MarkovProcess.ContinuousPath.exitTime U γ).toReal) :=
    ENNReal.measurable_toReal.comp (MarkovProcess.ContinuousPath.measurable_exitTime U hU)
  have hF : Measurable F := by
    apply Measurable.indicator _ (MarkovProcess.ContinuousPath.measurableSet_exitTime_lt_top U hU)
    exact (Real.measurable_exp.comp ((measurable_const.mul hτ).neg)).mul
      ((slabSmoothPayoff_smooth i c R).continuous.measurable.comp
        (MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop U hU))
  have hpoint (γ : Path d) : 0 ≤ F γ ∧ F γ ≤ 1 := by
    by_cases hγ : γ ∈ E
    · rw [show F γ = Real.exp (-(a * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
          slabSmoothPayoff i c R (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) from
          Set.indicator_of_mem hγ _]
      have hp := slabSmoothPayoff_mem_Icc i c R
        (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))
      have hw : Real.exp (-(a * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact neg_nonpos.mpr (mul_nonneg ha ENNReal.toReal_nonneg)
      exact ⟨mul_nonneg (Real.exp_pos _).le hp.1,
        (mul_le_mul_of_nonneg_right hw hp.1).trans (by simpa only [one_mul] using hp.2)⟩
    · simp only [F, Set.indicator_of_notMem hγ, le_refl, zero_le_one, and_self]
  have hint : Integrable F (G.pathLaw z) := Integrable.of_bound hF.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun γ => by rw [Real.norm_eq_abs, abs_of_nonneg (hpoint γ).1]; exact (hpoint γ).2)
  change (∫ γ, F γ ∂G.pathLaw z) ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact integral_nonneg fun γ => (hpoint γ).1
  · have h := integral_mono_ae hint (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun γ => (hpoint γ).2)
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] using h

/-- The discounted bounded-slab payoff converges to the actual payoff. -/
theorem gmp_discounted_slab_payoff_tendsto
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (c y z : Vec d) (N : ℝ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    let i := Renewal.forceCoord hd
    let U := coordinateSlab i c (l / μ) ∩ Metric.ball y N
    let f := slabSmoothPayoff i c (l / μ)
    Tendsto (fun n : ℕ => ∫ γ,
      {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
        (fun γ => Real.exp (-(a n * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
          f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ ∂G.pathLaw z) atTop
      (𝓝 (gmpBoundedSlabPayoff G i c (l / μ) y N z)) := by
  dsimp only
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let i := Renewal.forceCoord hd
  let U := coordinateSlab i c (l / μ) ∩ Metric.ball y N
  let f := slabSmoothPayoff i c (l / μ)
  have hfin : ∀ᵐ γ ∂G.pathLaw z, MarkovProcess.ContinuousPath.exitTime U γ < ⊤ := by
    filter_upwards [gmp_ae_source_slab_exit_ne_top d hd Λ r l hl Q μ hμ hμ1 ω hω G c z] with γ hγ
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hγ
      (MarkovProcess.ContinuousPath.exitTime_mono inter_subset_left γ))
  have h := tendsto_discounted_exitPayoff (G.pathLaw z) U
    ((isOpen_coordinateSlab i c (l / μ)).inter Metric.isOpen_ball) f
    (slabSmoothPayoff_smooth i c (l / μ)).continuous.measurable
    (fun x => (slabSmoothPayoff_mem_Icc i c (l / μ) x).1)
    (fun x => (slabSmoothPayoff_mem_Icc i c (l / μ) x).2) a ha ha0
  have heq : (∫ γ, {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
        (fun γ => f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ ∂G.pathLaw z) =
      gmpBoundedSlabPayoff G i c (l / μ) y N z := by
    apply integral_congr_ae
    filter_upwards [hfin] with γ hγ
    have hm : γ ∈ {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤} := hγ
    rw [Set.indicator_of_mem hm]
  rwa [heq] at h

end EinsteinFull.Regeneration
