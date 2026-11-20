import EinsteinFull.Regeneration.GMPUniformSlabEscape
import EinsteinFull.Regeneration.CappedSlabPositiveExit
import EinsteinFull.Calculus.SunaSuppliedLawIdentification

/-!
# Forward hitting from the positive slab-exit estimate

The uniform slab-survival bound and the positive-exit estimate of GMP
Lemma 4.3 give the forward-hitting bound of Lemma 4.2 for regular laws.
The positive-exit estimate remains an explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The uniform slab-exit bound removes the late-exit hypothesis from the
forward-hitting argument. The remaining hypothesis is GMP Lemma 4.3. -/
theorem uniform_regular_forward_hitting_of_positive_exit
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ g : ℝ, 0 < g ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω μ hμ.le hμ1),
        (∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ}) →
        ∀ (x : Vec d) (T : ℝ≥0) (a : ℝ), 0 ≤ a →
          G.pathLaw x {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Renewal.forceCoord hd) a} ≤
            ENNReal.ofReal (Real.exp (1 / 200) *
              Real.exp (-(1 / (400 * g)) * μ ^ 2 * (T : ℝ) + μ * a)) := by
  obtain ⟨n, hn⟩ := uniform_regular_gmp_slab_exit_tail d hd Λ r l hl
  let g : ℝ := n + 1
  have hg : 0 < g := by dsimp [g]; positivity
  refine ⟨g, hg, ?_⟩
  intro Q μ hμ hμ1 ω hω G hpositive x T a ha
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hcap : Real.toNNReal (g / μ ^ 2) =
      ((n + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta μ := by
    apply NNReal.coe_injective
    simp only [Real.coe_toNNReal _ (div_nonneg hg.le (sq_nonneg μ)), NNReal.coe_mul,
      NNReal.coe_natCast, Renewal.regenDelta,
      Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg μ))]
    dsimp [g]
    push_cast
    ring
  have hlate (y : Vec d) : (G.pathLaw y).real {γ |
      (Real.toNNReal (g / μ ^ 2) : ℝ≥0∞) <
        coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} ≤ (1 / 15 : ℝ) := by
    have hsub : {γ : Path d |
        (Real.toNNReal (g / μ ^ 2) : ℝ≥0∞) <
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} ⊆
        {γ : Path d | (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) <
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} := by
      intro γ hγ
      rw [hcap] at hγ
      apply (show (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) ≤
        ((((n + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) from by
          exact ENNReal.coe_le_coe.mpr (mul_le_mul_left (by exact_mod_cast Nat.le_succ n) _)).trans_lt hγ
    have hbound := (measure_mono hsub).trans (hn Q μ hμ hμ1 ω hω G y)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 15)] using hreal
  apply forward_hitting_le_of_regular_positive_exit hd (zeroPotentialReducedPair ω) μ
    (sourceReducedBound Λ) (one_le_sourceReducedBound Q.ellipticity_parameter) hω G.pathLaw
    (foundation_arbitrary_supplied_gmp_canonical_FDD hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1 G) x (Renewal.forceCoord hd) l g hμ (by linarith) hg
  · intro y
    exact cappedSlab_positive_probability_of_exit_bounds (G.pathLaw y) (Renewal.forceCoord hd)
      (l / μ) (div_pos (by linarith) hμ) _ (hpositive y) (hlate y)
  · exact ha

/-- GMP's positive-exit estimate gives forward hitting for every supplied reduced law. -/
theorem uniform_supplied_forward_hitting_of_positive_exit
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ g : ℝ, 0 < g ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d),
        IsGMPReducedKernel hd Q.ellipticity_parameter Q μ hμ.le hμ1 P →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ}) →
        ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (T : ℝ≥0) (a : ℝ), 0 ≤ a →
          P (x, ω) {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Renewal.forceCoord hd) a} ≤
            ENNReal.ofReal (Real.exp (1 / 200) *
              Real.exp (-(1 / (400 * g)) * μ ^ 2 * (T : ℝ) + μ * a)) := by
  obtain ⟨g, hg, hforward⟩ := uniform_regular_forward_hitting_of_positive_exit d hd Λ r l hl
  refine ⟨g, hg, ?_⟩
  intro Q μ hμ hμ1 P hP hpositive
  filter_upwards [hP, hpositive] with ω hω hp
  obtain ⟨hω, G, hrow⟩ := hω
  have hpositiveG : ∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
      coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
      γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
        (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ} := by
    intro y
    rw [← hrow y]
    exact hp y
  intro x T a ha
  rw [hrow x]
  exact hforward Q μ hμ hμ1 ω hω G hpositiveG x T a ha

end EinsteinFull.Regeneration
