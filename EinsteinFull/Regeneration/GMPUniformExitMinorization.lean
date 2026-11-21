import EinsteinFull.Calculus.SbxBCouplingSetwiseLowerR12
import EinsteinFull.Calculus.SbxASourceSetwiseDensityR05

/-!
# Uniform endpoint minorization for regular GMP paths

The local killed-kernel bounds and their finite chain yield the source
endpoint minorization for every regular realization, with a coefficient
chosen before the force and environment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Every regular reduced realization has the source endpoint minorization. -/
theorem uniform_regular_gmp_source_minorization
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω μ hμ.le hμ1),
        HasSourceMinorization (fun x => G.pathLaw x) (Renewal.regenDelta μ)
          δ (l / μ) (Renewal.forceCoord hd) := by
  obtain ⟨a, ha, hstep⟩ := b_coupling_local_steps d hd Λ r l hl
  obtain ⟨c, hc, hchain⟩ := b_coupling_setwise_of_local_chain a l ha
    (lt_of_lt_of_le zero_lt_one hl)
  obtain ⟨hδ, hδ1, hminor⟩ := SbxASourceSetwiseDensityR05.source_minorization_of_rescaled_setwise
    (Renewal.forceCoord hd) l c (lt_of_lt_of_le zero_lt_one hl) hc
  refine ⟨SbxS14MinorizationVolumeR03.windowCoinCoefficient (Renewal.forceCoord hd) l c,
    hδ, hδ1, ?_⟩
  intro Q μ hμ hμ1 ω hω G
  apply hminor μ hμ (Renewal.regenDelta μ) (fun x => G.pathLaw x)
  intro x
  exact hchain μ hμ G x (hstep Q μ hμ hμ1 ω hω G x)

end EinsteinFull.Regeneration
