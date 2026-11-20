import EinsteinFull.Regeneration.GMPExitSmoothPayoff
import EinsteinFull.Regeneration.ExitPayoffBounds

/-!
# The bounded-slab exit payoff

The actual reduced diffusion's bounded-domain exit payoff lies in the unit
interval and takes its prescribed values on both force faces.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Expected smooth payoff at exit from a slab intersected with a ball. -/
noncomputable def gmpBoundedSlabPayoff
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (y : Vec d) (N : ℝ) (z : Vec d) : ℝ :=
  ∫ γ, slabSmoothPayoff i c R (γ ((MarkovProcess.ContinuousPath.exitTimeTop
    (coordinateSlab i c R ∩ Metric.ball y N) γ).untopD 0)) ∂G.pathLaw z

/-- The bounded-slab payoff lies in the unit interval at every starting point. -/
theorem gmpBoundedSlabPayoff_mem_Icc
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (y : Vec d) (N : ℝ) (z : Vec d) :
    gmpBoundedSlabPayoff G i c R y N z ∈ Set.Icc (0 : ℝ) 1 := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  apply integral_exitPayoff_mem_Icc (G.pathLaw z)
    (coordinateSlab i c R ∩ Metric.ball y N) ((isOpen_coordinateSlab i c R).inter Metric.isOpen_ball)
    (slabSmoothPayoff i c R) (slabSmoothPayoff_smooth i c R).continuous.measurable
  · intro x
    exact (slabSmoothPayoff_mem_Icc i c R x).1
  · intro x
    exact (slabSmoothPayoff_mem_Icc i c R x).2

/-- The bounded-slab payoff is zero on the lower force face. -/
theorem gmpBoundedSlabPayoff_lower
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (hR : 0 < R) (y : Vec d) (N : ℝ) (z : Vec d)
    (hz : z i - c i = -R) : gmpBoundedSlabPayoff G i c R y N z = 0 := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hnot : z ∉ coordinateSlab i c R ∩ Metric.ball y N := by
    intro hm
    have hs := hm.1
    change |z i - c i| < R at hs
    rw [hz, abs_neg, abs_of_pos hR] at hs
    exact (lt_irrefl R) hs
  rw [gmpBoundedSlabPayoff, integral_exitPayoff_of_notMem (G.pathLaw z)
    (coordinateSlab i c R ∩ Metric.ball y N) z hnot (slabSmoothPayoff i c R) (G.pathLaw_starts_at z)]
  exact slabSmoothPayoff_lower i c R z hz

/-- The bounded-slab payoff is one on the upper force face. -/
theorem gmpBoundedSlabPayoff_upper
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (R : ℝ) (hR : 0 < R) (y : Vec d) (N : ℝ) (z : Vec d)
    (hz : z i - c i = R) : gmpBoundedSlabPayoff G i c R y N z = 1 := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hnot : z ∉ coordinateSlab i c R ∩ Metric.ball y N := by
    intro hm
    have hs := hm.1
    change |z i - c i| < R at hs
    rw [hz, abs_of_pos hR] at hs
    exact (lt_irrefl R) hs
  rw [gmpBoundedSlabPayoff, integral_exitPayoff_of_notMem (G.pathLaw z)
    (coordinateSlab i c R ∩ Metric.ball y N) z hnot (slabSmoothPayoff i c R) (G.pathLaw_starts_at z)]
  exact slabSmoothPayoff_upper i c R hR z hz

end EinsteinFull.Regeneration
