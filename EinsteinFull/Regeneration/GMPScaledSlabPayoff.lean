import EinsteinFull.Regeneration.GMPBoundedSlabPayoff

/-!
# Rescaled bounded-slab payoff

The physical slab payoff, translated and rescaled to unit force, retains its
unit bounds and the force-face boundary values.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The bounded-slab payoff in translated, rescaled coordinates. -/
noncomputable def gmpScaledSlabPayoff
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (l μ : ℝ) (y : Vec d) (N : ℝ) (z : Vec d) : ℝ :=
  gmpBoundedSlabPayoff G i c (l / μ) y N (c + μ⁻¹ • z)

/-- The rescaled payoff remains in the unit interval. -/
theorem gmpScaledSlabPayoff_mem_Icc
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (l μ : ℝ) (y : Vec d) (N : ℝ) (z : Vec d) :
    gmpScaledSlabPayoff G i c l μ y N z ∈ Set.Icc (0 : ℝ) 1 :=
  gmpBoundedSlabPayoff_mem_Icc G i c (l / μ) y N (c + μ⁻¹ • z)

/-- The rescaled payoff vanishes on the lower force face. -/
theorem gmpScaledSlabPayoff_lower
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (l μ : ℝ) (hl : 0 < l) (hμ : 0 < μ)
    (y : Vec d) (N : ℝ) (z : Vec d) (hz : z i = -l) :
    gmpScaledSlabPayoff G i c l μ y N z = 0 := by
  apply gmpBoundedSlabPayoff_lower G i c (l / μ) (div_pos hl hμ) y N
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz]
  ring

/-- The rescaled payoff equals one on the upper force face. -/
theorem gmpScaledSlabPayoff_upper
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (l μ : ℝ) (hl : 0 < l) (hμ : 0 < μ)
    (y : Vec d) (N : ℝ) (z : Vec d) (hz : z i = l) :
    gmpScaledSlabPayoff G i c l μ y N z = 1 := by
  apply gmpBoundedSlabPayoff_upper G i c (l / μ) (div_pos hl hμ) y N
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz]
  ring

/-- The rescaled payoff at the origin is the original payoff at its center. -/
theorem gmpScaledSlabPayoff_zero
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (i : Fin d) (c : Vec d) (l μ : ℝ) (y : Vec d) (N : ℝ) :
    gmpScaledSlabPayoff G i c l μ y N 0 = gmpBoundedSlabPayoff G i c (l / μ) y N c := by
  simp only [gmpScaledSlabPayoff, smul_zero, add_zero]

end EinsteinFull.Regeneration
