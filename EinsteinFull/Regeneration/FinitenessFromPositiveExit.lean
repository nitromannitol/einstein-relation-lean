import EinsteinFull.Regeneration.NoReturnFromPositiveExit
import EinsteinFull.Regeneration.FirstRegenerationFiniteness
import EinsteinFull.Regeneration.UniformReturnAtGrid

/-!
# First-regeneration finiteness from positive slab exits

GMP's positive-exit estimate at one fixed scale gives both the hitting
and no-backtracking estimates needed for first-regeneration finiteness.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- GMP's positive-exit estimate implies finite first regeneration at large scales. -/
theorem first_regeneration_finite_of_positive_slab_exit
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ l₀ : ℝ, 0 < l₀ ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (l δ : ℝ), l₀ ≤ l → r < 2 * l → 0 < δ → δ < 1 →
        ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
        IsRegenerationCoupling hd Q μ l δ hμ.le hμ1 P K →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
          firstRegenerationTime (Renewal.regenDelta μ) μ (l / μ) q.2
            (Renewal.forceCoord hd) ≠ ⊤ := by
  obtain ⟨l₀, hl₀, hback⟩ := uniform_no_backtracking_of_positive_slab_exit d hd Λ r L hL
  obtain ⟨g, hg, hforward⟩ := uniform_supplied_forward_hitting_of_positive_exit d hd Λ r L hL
  refine ⟨l₀, hl₀, ?_⟩
  intro Q μ hμ hμ1 l δ hl hsep hδ0 hδ1 P K hK hpositive
  have hlt : 0 < l := lt_of_lt_of_le hl₀ hl
  have hback' : ∀ᵐ ω ∂Q.measure, ∀ x, ENNReal.ofReal (1 / 2 : ℝ) ≤
      P (x, ω) {γ | NoBacktracking (l / μ) γ (Renewal.forceCoord hd)} := by
    filter_upwards [hback Q μ hμ hμ1 P hK.2.2.1 hpositive] with ω hω
    exact hω l hl
  have hreturn := trial_return_estimate_of_uniform_no_backtracking hd Q μ hμ hμ1 l δ hlt
    P K hK (1 / 2) (by norm_num) hback'
  have hhit : ∀ (T : ℝ≥0) (a : ℝ), 0 ≤ a → ∀ᵐ ω ∂Q.measure,
      P (0, ω) {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Renewal.forceCoord hd) a} ≤
        ENNReal.ofReal (Real.exp (1 / 200) *
          Real.exp (-(1 / (400 * g)) * μ ^ 2 * T + μ * a)) := by
    intro T a ha
    filter_upwards [hforward Q μ hμ hμ1 P hK.2.2.1 hpositive] with ω hω
    exact hω 0 T a ha
  exact first_regeneration_finite_of_hitting_and_return hd Q μ hμ hμ1 l δ hlt hsep
    hδ0 hδ1 P K hK (1 / (400 * g)) (Real.exp (1 / 200)) (by positivity)
    hhit (1 / 2) (by norm_num) (by norm_num) hreturn

end EinsteinFull.Regeneration
