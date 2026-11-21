import EinsteinFull.Regeneration.SlabExitFromSuccessfulRuns
import EinsteinFull.Regeneration.FreshSuccessfulRuns
import EinsteinFull.Blueprint.G1.Proofs.S3MRenewal

/-!
# Slab exits under the coupled law

Fresh successful bridge runs force every shifted coordinate slab exit to be
finite for the actual regeneration coupling.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Every shifted force-coordinate slab exit is finite under the regeneration coupling. -/
theorem ae_shifted_coordinate_slab_exit_finite {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (r : ℝ) (t : ℝ≥0),
      coordinateSlabExit (pathTimeShift q.2.1 t) (Renewal.forceCoord hd) r ≠ ⊤ := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hruns := ae_arbitrarily_late_successful_runs Q.measure K hK.1
    (Renewal.regenDelta lam) δ hδ hδ1 hK.2.2.2.1
  have hgain := EinsteinFull.Blueprint.ae_gain_annealed hd Q lam h0 h1 l δ P K hK
  filter_upwards [hruns, hgain] with q hq hg r t
  exact coordinate_slab_exit_finite_of_successful_runs q.2.1 q.2.2 (Renewal.forceCoord hd)
    (Renewal.regenDelta lam) (EinsteinRelation.regenDelta_pos h0) (l / lam) r
    (div_pos hl h0) hg hq t

/-- All successive slab exits are finite on one event under the coupled law. -/
theorem ae_successive_coordinate_slab_exits_finite {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (r : ℝ) (n : ℕ),
      coordinateSlabExit
        (pathTimeShift q.2.1 (successiveSlabExitTime q.2.1 (Renewal.forceCoord hd) r n))
        (Renewal.forceCoord hd) r ≠ ⊤ := by
  filter_upwards [ae_shifted_coordinate_slab_exit_finite hd Q lam h0 h1 l δ hl hδ hδ1 P K hK]
    with q hq r n
  exact hq r _

end EinsteinFull.Regeneration
