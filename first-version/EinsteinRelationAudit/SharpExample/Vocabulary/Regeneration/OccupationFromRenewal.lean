import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import EinsteinRelationAudit.SharpExample.Vocabulary.Carriers.DensityAnnealedTwins
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.GMPFamily
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.External.GantertSection7Support
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.LocalSigma
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ProbabilityPart
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ReductionLocality
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ValidAnnealedLawSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.Construction
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.Coupling
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.OccupationLaterIntervals
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.RenewalCarriers

/-! Restated from the library module `EinsteinRelation.Regeneration.OccupationFromRenewal`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
open scoped NNReal ENNReal
open EinsteinRelation.External.GantertSection7Support (GantertFixedEnvironmentRealization)
noncomputable section
namespace EinsteinRelation
/-- Lemma 3.1 (`regen.renewal`, `paper/main.tex` lines 348–354) in quantifier form: for every
`d ≥ 2` and environment constants there is a threshold `l₀` with `r₀ < 2 l₀` such that
`RenewalLemma31At` holds for every environment law at `l₀`. This is the production twin of
`EinsteinRelation.regeneration_renewal`. -/
def RenewalLemma31Input : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ Q : EnvironmentLaw d Λ₀ r₀, RenewalLemma31At hd Q l₀
/-- Existence of the GMP Section 7 coupling (Gantert–Mathieu–Piatnitski 2012, Proposition 5.4,
p. 23, with the measurable-coefficient extension of Section 7, p. 32). The success
probability `δ` is chosen after `l`,
and the realization `(P, K)` exists for every environment law and force. -/
def GMPCouplingExistsV2Input : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∃ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
        Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ hl0.le hl1 P K
/-- The no-backtracking mass lower bound and the first regeneration tail (Gantert–Mathieu–Piatnitski
2012, Lemmas 5.7 and 5.8, pp. 25–26, and (5.20), p. 25, with Section 7, p. 32). The
constant `c` depends on
`d`, `Λ₀`, `r₀`, `δ` and `l`, and not on `λ`, the environment law, `P` or `K`. -/
def GMPCouplingTailsV2Input : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ c C : ℝ, 0 < c ∧
        ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
        ∀ Q : EnvironmentLaw d Λ₀ r₀,
        ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
          Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ hl0.le hl1 P K →
          Regeneration.HasNoBacktrackingMass Q.measure (l / lam) c
              (Regeneration.Renewal.forceCoord hd) K ∧
            Regeneration.HasFirstRegenerationTail Q.measure (Regeneration.Renewal.regenDelta lam)
              lam (l / lam) c C (Regeneration.Renewal.forceCoord hd) K
end EinsteinRelation
end
