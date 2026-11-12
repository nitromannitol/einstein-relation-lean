import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Exponential
import EinsteinRelationAudit.SharpExample.Vocabulary.Carriers.DensityAnnealedTwins
import EinsteinRelationAudit.SharpExample.Vocabulary.Carriers.RegenerationCorrectorTwins
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.GMPFamily
import EinsteinRelationAudit.SharpExample.Vocabulary.External.GantertSection7Support
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.LocalSigma
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ProbabilityPart
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ReductionLocality
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.ValidAnnealedLawSupport
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.Construction
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.RenewalCarriers

/-! Restated from the library module `EinsteinRelation.Regeneration.OccupationLaterIntervals`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation
/-- Lemma 3.1 (`regen.renewal`, `paper/main.tex` lines 348–354) at the threshold `l₀`, in the
production form of `EinsteinRelation.regeneration_renewal`. The coupled path law input is replaced by
the environment law `Q` and the coupled kernel `K`, with `I.Q = Q.measure` built in, and the frozen
names by their production twins. The frozen statement is
`∀ d hd Λ₀ r₀, ∃ l₀, r₀ < 2 l₀ ∧ ∀ Q, RenewalLemma31At hd Q l₀`. -/
def RenewalLemma31At {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (l₀ : ℝ) :
    Prop :=
  ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
      ∀ hGMP : Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ
        hl0.le hl1 P K,
      ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
          (Carriers.cycleConditioningEvent hd (l / lam)) ≠ 0,
      ∀ k : ℕ, 1 ≤ k →
        AEMeasurable (Regeneration.Renewal.cycleRecord hd lam l k)
          (Regeneration.annealedCoupledLaw Q.measure K) ∧
        AEMeasurable (Regeneration.Renewal.cycleRecord hd lam l 0)
          (Regeneration.annealedCoupledLaw Q.measure K) ∧
        ∀ Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ,
          Measurable Φ → Regeneration.BoundedRealTest Φ →
          (∫ ωz, Φ (Regeneration.Renewal.cycleRecord hd lam l k ωz)
              ∂(Regeneration.annealedCoupledLaw Q.measure K)) =
            ∫ ωz, Φ (Regeneration.Renewal.cycleRecord hd lam l 0 ωz)
              ∂((Carriers.cycleConditionedLaw Q.measure K hGMP.1 hd (l / lam) hD).1)
end EinsteinRelation
end
