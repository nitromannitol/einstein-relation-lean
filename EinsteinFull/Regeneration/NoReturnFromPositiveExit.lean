import EinsteinFull.Regeneration.GMPBackwardFromPositiveExit
import EinsteinFull.Regeneration.NoReturnFromHitting

/-!
# No return from positive slab exits

The positive slab-exit estimate at one fixed comparison scale yields
the no-return bound at every sufficiently large regeneration scale.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Positive exits at a fixed scale imply a uniform annealed no-return bound. -/
theorem no_return_of_positive_slab_exit
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ l₀ : ℝ, 0 < l₀ ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (l δ : ℝ) (_hl : l₀ ≤ l) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
        IsRegenerationCoupling hd Q μ l δ hμ.le hμ1 P K →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ENNReal.ofReal (1 / 2 : ℝ) ≤
          annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / μ)) := by
  obtain ⟨κ, C, hκ, hC, hback⟩ := uniform_supplied_backward_hitting_of_positive_exit d hd Λ r L hL
  let l₀ : ℝ := max 1 (2 * C / κ)
  have hl₀ : 0 < l₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨l₀, hl₀, ?_⟩
  intro Q μ hμ hμ1 l δ hl P K hK hpositive
  have hlbound : 2 * C ≤ κ * l := by
    have h := (div_le_iff₀ hκ).mp ((le_max_right 1 (2 * C / κ)).trans hl)
    nlinarith
  have hexp : C * Real.exp (-κ * l) ≤ (1 / 2 : ℝ) := by
    have he := Real.add_one_le_exp (κ * l)
    have hpos : 0 < Real.exp (κ * l) := Real.exp_pos _
    rw [show -κ * l = -(κ * l) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith
  have : IsProbabilityMeasure Q.measure := Q.probability
  apply no_return_mass_of_backtracking_bound hd Q.measure P K hK.1 hK.2.1 (l / μ)
  filter_upwards [hback Q μ hμ hμ1 P hK.2.2.1 hpositive] with ω hω
  calc
    P (0, ω) {γ | firstHittingBelow γ (Renewal.forceCoord hd) (-(l / μ)) ≠ ⊤} ≤
        ENNReal.ofReal (C * Real.exp (-κ * μ * (l / μ))) := hω 0 _
    _ = ENNReal.ofReal (C * Real.exp (-κ * l)) := by congr 2; field_simp
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hexp

end EinsteinFull.Regeneration
