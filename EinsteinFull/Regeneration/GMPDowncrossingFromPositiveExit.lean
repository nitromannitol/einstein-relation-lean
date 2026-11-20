import EinsteinFull.Regeneration.GMPBackwardFromPositiveExit
import EinsteinFull.Regeneration.CoupledDowncrossingContraction

/-!
# Downcrossing contraction from positive exits

The positive slab-exit estimate gives the uniform failed-downcrossing
exponential-moment contraction used in Shen's renewal argument.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Positive exits imply a uniform contraction of failed-downcrossing moments. -/
theorem uniform_coupled_downcrossing_contraction_of_positive_exit
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ a l₀ : ℝ, 0 < a ∧ 0 < l₀ ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω μ hμ.le hμ1),
        (∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ∀ (x : Vec d) (ν : Measure (CoupledSample d)), ν.map Prod.fst = G.pathLaw x →
        ∀ l : ℝ, l₀ ≤ l →
        let E := {z : CoupledSample d |
          firstHittingBelow z.1 (Renewal.forceCoord hd) (-(l / μ)) ≠ ⊤}
        let F := fun z : CoupledSample d => Real.exp (a * μ *
          coordinateMaximum z.1 (Renewal.forceCoord hd)
            (firstHittingBelow z.1 (Renewal.forceCoord hd) (-(l / μ))).toNNReal)
        Integrable (E.indicator F) ν ∧ (∫ z, E.indicator F z ∂ν) ≤ (3 / 4 : ℝ) := by
  obtain ⟨κ, C, hκ, hC, hback⟩ := uniform_regular_backward_hitting_of_positive_exit d hd Λ r L hL
  obtain ⟨a, ha, hcontract⟩ := coupled_downcrossing_overshoot_moment_contraction κ C hκ hC.le
  let l₀ : ℝ := max 1 (2 * C / κ)
  have hl₀ : 0 < l₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨a, l₀, ha, hl₀, ?_⟩
  intro Q μ hμ hμ1 ω hω G hpositive x ν hpath l hl
  have hscale : 2 * C ≤ κ * l := by
    have h := (div_le_iff₀ hκ).mp ((le_max_right 1 (2 * C / κ)).trans hl)
    nlinarith
  have hexp : C * Real.exp (-κ * l) ≤ (1 / 2 : ℝ) := by
    have he := Real.add_one_le_exp (κ * l)
    have hpos : 0 < Real.exp (κ * l) := Real.exp_pos _
    rw [show -κ * l = -(κ * l) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith
  have hb := hback Q μ hμ hμ1 ω hω G hpositive
  have hfail : G.pathLaw x {γ |
      firstHittingBelow γ (Renewal.forceCoord hd) (-(l / μ)) ≠ ⊤} ≤
        ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (C * Real.exp (-κ * μ * (l / μ))) := hb x _
      _ = ENNReal.ofReal (C * Real.exp (-κ * l)) := by congr 2; field_simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hexp
  apply hcontract hd (zeroPotentialReducedPair ω) μ (sourceReducedBound Λ)
    (one_le_sourceReducedBound Q.ellipticity_parameter) hω hμ hμ1 G x ν hpath
    (Renewal.forceCoord hd) (l / μ) (div_nonneg (lt_of_lt_of_le hl₀ hl).le hμ.le)
  · intro y u _
    exact hb y u
  · exact hfail

end EinsteinFull.Regeneration
