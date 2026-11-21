import EinsteinFull.Regeneration.GMPExitSmoothPayoff
import EinsteinFull.Regeneration.GMPDiscountedPayoff
import EinsteinFull.Regeneration.SlabCompactPayoff

/-!
# Compact payoffs for bounded slab exits

On a bounded open domain a path exits in the closure, so compactly supported
extensions reproduce the smooth slab payoff at exit.
-/

open Filter MeasureTheory Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- At a finite exit from an open subset of a ball, equal payoffs on its closed ball agree. -/
theorem exit_payoff_eq_of_eqOn_closedBall {α : Type*} [PseudoMetricSpace α]
    (U : Set α) (hU : IsOpen U) (y : α) (N : ℝ) (hsub : U ⊆ Metric.ball y N)
    (f g : α → ℝ) (hfg : Set.EqOn f g (Metric.closedBall y N))
    (γ : MarkovProcess.ContinuousPath α) (hstart : γ 0 ∈ U)
    (hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) =
      g (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) := by
  have hfront := MarkovProcess.ContinuousPath.coordinate_exitTime_mem_frontier U hU γ hstart hfin
  have hclosed : γ (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal ∈ Metric.closedBall y N :=
    closure_minimal (hsub.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall hfront.1
  rw [MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal U γ hfin]
  exact hfg hclosed

/-- Discounted finite-exit payoffs agree when their boundary values agree. -/
theorem discounted_exit_payoff_eq_of_eqOn_closedBall {α : Type*} [PseudoMetricSpace α]
    (U : Set α) (hU : IsOpen U) (y : α) (N a : ℝ) (hsub : U ⊆ Metric.ball y N)
    (f g : α → ℝ) (hfg : Set.EqOn f g (Metric.closedBall y N))
    (γ : MarkovProcess.ContinuousPath α) (hstart : γ 0 ∈ U) :
    {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
      (fun γ => Real.exp (-(a * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
        f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ =
    {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
      (fun γ => Real.exp (-(a * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
        g (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ := by
  by_cases hfin : MarkovProcess.ContinuousPath.exitTime U γ < ⊤
  · have hm : γ ∈ {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤} := hfin
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm,
      exit_payoff_eq_of_eqOn_closedBall U hU y N hsub f g hfg γ hstart
        (lt_top_iff_ne_top.mp hfin)]
  · have hm : γ ∉ {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤} := hfin
    simp only [Set.indicator_of_notMem hm]

/-- One compact extension represents every discounted exit payoff from the bounded slab. -/
theorem exists_compact_smooth_gmp_discounted_exit_payoff
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (y : Vec d) (N : ℝ) :
    let U := coordinateSlab i c R ∩ Metric.ball y N
    ∃ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      ∀ (a : ℝ) (z : Vec d), z ∈ U → gmpDiscountedSlabPayoff G i c R y N a z =
        ∫ γ, {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
          (fun γ => Real.exp (-(a * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
            f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ ∂G.pathLaw z := by
  dsimp only
  let U := coordinateSlab i c R ∩ Metric.ball y N
  obtain ⟨f, hf, hc, hb, heq⟩ := exists_compact_smooth_slabPayoff i c y R N
  refine ⟨f, hf, hc, hb, ?_⟩
  intro a z hz
  unfold gmpDiscountedSlabPayoff
  apply integral_congr_ae
  filter_upwards [G.pathLaw_starts_at z] with γ hstart
  change γ 0 = z at hstart
  exact (discounted_exit_payoff_eq_of_eqOn_closedBall U
    ((isOpen_coordinateSlab i c R).inter Metric.isOpen_ball) y N a inter_subset_right
    f (slabSmoothPayoff i c R) heq γ (hstart ▸ hz)).symm

/-- A compact smooth payoff gives the same bounded-domain exit expectation. -/
theorem exists_compact_smooth_gmp_exit_payoff
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (x y : Vec d) (N : ℝ) (hx : x ∈ Metric.ball y N) :
    let i := Renewal.forceCoord hd
    let U := coordinateSlab i x (l / μ) ∩ Metric.ball y N
    ∃ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      (∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) ∂G.pathLaw x) =
      ∫ γ, slabSmoothPayoff i x (l / μ)
        (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) ∂G.pathLaw x := by
  dsimp only
  let i := Renewal.forceCoord hd
  let U := coordinateSlab i x (l / μ) ∩ Metric.ball y N
  obtain ⟨f, hf, hc, hb, heq⟩ := exists_compact_smooth_slabPayoff i x y (l / μ) N
  refine ⟨f, hf, hc, hb, ?_⟩
  apply integral_congr_ae
  filter_upwards [G.pathLaw_starts_at x,
    gmp_ae_source_slab_exit_ne_top d hd Λ r l hl Q μ hμ hμ1 ω hω G x x] with γ hstart hfin
  change γ 0 = x at hstart
  have hR : 0 < l / μ := div_pos (lt_of_lt_of_le zero_lt_one hl) hμ
  have hγ : γ 0 ∈ U := by
    rw [hstart]
    exact ⟨by simpa [coordinateSlab] using hR, hx⟩
  have hfin' : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤ := by
    exact ne_top_of_le_ne_top hfin (MarkovProcess.ContinuousPath.exitTime_mono inter_subset_left γ)
  exact exit_payoff_eq_of_eqOn_closedBall U ((isOpen_coordinateSlab i x (l / μ)).inter Metric.isOpen_ball)
    y N inter_subset_right f (slabSmoothPayoff i x (l / μ)) heq γ hγ hfin'

end EinsteinFull.Regeneration
