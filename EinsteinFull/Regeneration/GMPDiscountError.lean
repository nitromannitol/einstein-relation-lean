import EinsteinFull.Regeneration.DiscountErrorBound
import EinsteinFull.Regeneration.GMPSlabExitMoment
import EinsteinFull.Regeneration.GMPDiscountedPayoff

/-!
# Uniform discount error for slab exits

The scaled exit-time moment controls the error of discounting at a rate
proportional to the force squared, uniformly over bounded source slabs.
-/

open MeasureTheory ProbabilityTheory Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Scaled discount errors for bounded source-slab payoffs are uniformly linear. -/
theorem uniform_regular_gmp_slab_discount_error
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω μ hμ.le hμ1) (c x y : Vec d) (N a : ℝ), 0 ≤ a →
        let i := Renewal.forceCoord hd
        0 ≤ gmpBoundedSlabPayoff G i c (l / μ) y N x -
          gmpDiscountedSlabPayoff G i c (l / μ) y N (a * μ ^ 2) x ∧
        gmpBoundedSlabPayoff G i c (l / μ) y N x -
          gmpDiscountedSlabPayoff G i c (l / μ) y N (a * μ ^ 2) x ≤ a * C := by
  obtain ⟨δ, hδ, hδ1, hmean⟩ := uniform_regular_gmp_slab_exit_mean d hd Λ r l hl
  let C := (Real.exp δ * Real.exp (δ / 4) / (1 - Real.exp (δ / 4 - δ / 2))) / (δ / 4)
  have hden : 0 < 1 - Real.exp (δ / 4 - δ / 2) := by
    have h := Real.exp_lt_one_iff.mpr (by linarith : δ / 4 - δ / 2 < 0)
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q μ hμ hμ1 ω hω G c x y N a ha
  dsimp only
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let i := Renewal.forceCoord hd
  let U := coordinateSlab i c (l / μ) ∩ Metric.ball y N
  have hU : IsOpen U := (isOpen_coordinateSlab i c (l / μ)).inter Metric.isOpen_ball
  obtain ⟨hSi, hSb⟩ := hmean Q μ hμ hμ1 ω hω G c x U hU inter_subset_left
  let S : Path d → ℝ := fun γ => μ ^ 2 * (MarkovProcess.ContinuousPath.exitTime U γ).toReal
  let F : Path d → ℝ := fun γ => slabSmoothPayoff i c (l / μ)
    (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))
  have hSm : Measurable S := measurable_const.mul
    ((MarkovProcess.ContinuousPath.measurable_exitTime U hU).ennreal_toReal)
  have hFm : Measurable F := (slabSmoothPayoff_smooth i c (l / μ)).continuous.measurable.comp
    (MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop U hU)
  have hF0 : ∀ γ, 0 ≤ F γ := fun γ => (slabSmoothPayoff_mem_Icc i c (l / μ) _).1
  have hF1 : ∀ γ, F γ ≤ 1 := fun γ => (slabSmoothPayoff_mem_Icc i c (l / μ) _).2
  have hS0 : ∀ γ, 0 ≤ S γ := fun _ => mul_nonneg (sq_nonneg μ) ENNReal.toReal_nonneg
  have herror := integral_discount_error_le (G.pathLaw x) S F hSm hSi hS0 hFm hF0 hF1 a ha
  have hfin : ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ < ⊤ := by
    filter_upwards [gmp_ae_source_slab_exit_ne_top d hd Λ r l hl Q μ hμ hμ1 ω hω G c x] with γ hγ
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hγ
      (MarkovProcess.ContinuousPath.exitTime_mono inter_subset_left γ))
  have hdiscount : gmpDiscountedSlabPayoff G i c (l / μ) y N (a * μ ^ 2) x =
      ∫ γ, Real.exp (-(a * S γ)) * F γ ∂G.pathLaw x := by
    unfold gmpDiscountedSlabPayoff
    apply integral_congr_ae
    filter_upwards [hfin] with γ hγ
    have hm : γ ∈ {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤} := hγ
    rw [Set.indicator_of_mem hm]
    congr 2
    dsimp [S]
    ring
  change 0 ≤ (∫ γ, F γ ∂G.pathLaw x) - _ ∧ (∫ γ, F γ ∂G.pathLaw x) - _ ≤ a * C
  rw [hdiscount]
  exact ⟨herror.1, herror.2.trans (mul_le_mul_of_nonneg_left hSb ha)⟩

end EinsteinFull.Regeneration
