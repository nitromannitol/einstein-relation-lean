import EinsteinFull.Regeneration.GMPUniformSlabEscape

/-!
# Geometric tail for source slab exits

The uniform source minorization and killed semigroup give a geometric
survival bound at every multiple of the regeneration time scale.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Source slab survival decays geometrically, uniformly over regular laws and starts. -/
theorem uniform_regular_gmp_slab_exit_geometric
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω μ hμ.le hμ1) (c x : Vec d) (n : ℕ),
      G.pathLaw x {γ : Path d |
        (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) <
          MarkovProcess.ContinuousPath.exitTime
            (coordinateSlab (Renewal.forceCoord hd) c (l / μ)) γ} ≤
        ENNReal.ofReal (1 - δ) ^ n := by
  obtain ⟨δ, hδ, hδ1, hminor⟩ := uniform_regular_gmp_source_minorization d hd Λ r l hl
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro Q μ hμ hμ1 ω hω G c x n
  let i := Renewal.forceCoord hd
  let R := l / μ
  let Δ := Renewal.regenDelta μ
  let U := coordinateSlab i c R
  have hR : 0 < R := div_pos (lt_of_lt_of_le zero_lt_one hl) hμ
  have hstep : ∀ y, G.pathLaw y {γ : Path d |
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U} ≤ ENNReal.ofReal (1 - δ) :=
    gmp_slab_survival_le_of_source_minorization G Δ δ R i hδ hδ1.le hR
      (hminor Q μ hμ hμ1 ω hω G) c
  have hsurv := gmp_survival_le_pow G U (isOpen_coordinateSlab i c R) Δ
    (ENNReal.ofReal (1 - δ)) hstep n x
  refine (measure_mono ?_).trans hsurv
  intro γ hγ t ht
  exact MarkovProcess.ContinuousPath.mem_of_lt_exitTime U γ t
    ((ENNReal.coe_le_coe.mpr ht).trans_lt hγ)

end EinsteinFull.Regeneration
