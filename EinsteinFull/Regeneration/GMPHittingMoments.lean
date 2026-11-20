import EinsteinFull.Regeneration.ScaledHittingMoment
import EinsteinFull.Regeneration.GMPForwardFromPositiveExit

/-!
# Scaled hitting moments from positive slab exits

Gantert–Mathieu–Piatnitski's forward-hitting estimate, obtained from their
Lemma 4.3, bounds the scaled time to reach a level of order `1 / lam`.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.Diffusion EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Positive slab exits give uniform exponential moments for scaled first hitting times. -/
theorem uniform_regular_hitting_moment_of_positive_exit
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ g : ℝ, 0 < g ∧
      ∀ b : ℝ, 0 ≤ b →
      ∀ (Q : EnvironmentLaw d Λ r) (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω lam hlam.le hlam1),
        (∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / lam) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / lam)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / lam}) →
        ∀ x : Vec d,
          Integrable (fun γ => Real.exp ((1 / (1600 * g)) * (lam ^ 2 *
            (firstHittingAbove γ (Renewal.forceCoord hd) (b / lam)).toReal))) (G.pathLaw x) ∧
          (∫ γ, Real.exp ((1 / (1600 * g)) * (lam ^ 2 *
            (firstHittingAbove γ (Renewal.forceCoord hd) (b / lam)).toReal)) ∂G.pathLaw x) ≤
              max 1 (Real.exp (1 / 200) * Real.exp b) * Real.exp (1 / (1600 * g)) /
                (1 - Real.exp ((1 / (1600 * g)) - (1 / (400 * g)) / 2)) := by
  obtain ⟨g, hg, hforward⟩ := uniform_regular_forward_hitting_of_positive_exit d hd Λ r L hL
  refine ⟨g, hg, ?_⟩
  intro b hb Q lam hlam hlam1 ω hω G hpositive x
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let τ := fun γ : Path d => firstHittingAbove γ (Renewal.forceCoord hd) (b / lam)
  have hτ : Measurable τ := (measurable_firstHittingAbove (Renewal.forceCoord hd)).comp
    (measurable_const.prodMk measurable_id)
  have ha : 0 < 1 / (1600 * g) := by positivity
  have haκ : 1 / (1600 * g) < (1 / (400 * g)) / 2 := by
    have hinv : 0 < g⁻¹ := inv_pos.mpr hg
    field_simp
    nlinarith
  apply scaled_time_exponential_moment_of_tail (G.pathLaw x) τ hτ (lam ^ 2)
    (1 / (400 * g)) (Real.exp (1 / 200)) b (1 / (1600 * g))
    (by positivity) (Real.exp_pos _).le ha haκ
  intro t ht
  have h := hforward Q lam hlam hlam1 ω hω G hpositive x t.toNNReal (b / lam)
    (div_nonneg hb hlam.le)
  rw [ENNReal.ofReal_eq_coe_nnreal ht]
  have heq : -(1 / (400 * g)) * lam ^ 2 * (t.toNNReal : ℝ) + lam * (b / lam) =
      -(1 / (400 * g)) * lam ^ 2 * t + b := by
    rw [Real.coe_toNNReal _ ht]
    field_simp
  have hnn : t.toNNReal = ⟨t, ht⟩ := by
    ext
    exact Real.coe_toNNReal _ ht
  rw [heq, hnn] at h
  exact h

end EinsteinFull.Regeneration
