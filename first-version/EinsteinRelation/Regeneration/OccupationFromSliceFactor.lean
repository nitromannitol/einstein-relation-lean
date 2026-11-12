import EinsteinRelation.Regeneration.RenewalFromSliceFactor
import EinsteinRelation.Regeneration.OccupationFromFrozenInputs

/-!
# Exact production targets after the deterministic slice identity

Source `paper/main.tex:411–432,445–517`. This module discharges the renewal
summation, conditional invariance, iteration, finiteness and occupation
assembly. The kernel-locality and slice-factorization argument remains an
explicit internal obligation. No theorem here asserts that this obligation
is a frozen external input.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation

/-- The still-internal slice-factorization assertion (`paper/main.tex:411–415`),
uniform over the same concrete couplings as Lemma 3.1. -/
def FirstRegenerationSliceFactorInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ l : ℝ, l₀ ≤ l →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
        ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
          Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ
            hl0.le hl1 P K →
          Regeneration.FirstRegenerationSliceFactor Q.measure K
            (Regeneration.Renewal.regenDelta lam) lam (l / lam) (Regeneration.Renewal.forceCoord hd)

/-- Lemma 3.1 with the precise production statement, after the slice identity
(`paper/main.tex:411–432`). The cited tail supplies only first-time finiteness;
later finiteness and conditional invariance are proved by record iteration. -/
theorem renewalLemma31Input_of_slice_factor_and_tails
    (hSlice : FirstRegenerationSliceFactorInput) (hTail : GMPCouplingTailsV2Input) :
    RenewalLemma31Input := by
  intro d hd Λ₀ r₀
  obtain ⟨lS, hlS, hS⟩ := hSlice d hd Λ₀ r₀
  obtain ⟨lT, _, hT⟩ := hTail d hd Λ₀ r₀
  refine ⟨max lS (max lT 1), lt_of_lt_of_le hlS (by gcongr; exact le_max_left _ _), ?_⟩
  intro Q l hl δ hδ0 hδ1 lam hl0 hl1 P K hGMP hD k hk
  have hlS' : lS ≤ l := (le_max_left _ _).trans hl
  have hlT' : lT ≤ l := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hl
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one
    ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hl)
  have hR : 0 < l / lam := div_pos hlpos hl0
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    regenDelta_pos hl0
  obtain ⟨c, C, hc, htail⟩ := hT l hlT' δ hδ0 hδ1
  have hfin := Regeneration.firstRegenerationTime_ne_top_ae_of_tail Q.measure K
    (Regeneration.Renewal.regenDelta lam) lam (l / lam) c C hc hl0
    (Regeneration.Renewal.forceCoord hd) (htail lam hl0 hl1 Q P K hGMP).2
  have hsupport := hGMP.2.2.2.2.2.1
  have hren := Regeneration.renewal_marginals_of_slice_factor Q.measure K hGMP.1
    (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) hl0 hR
    (Regeneration.Renewal.forceCoord hd) hsupport hfin hD
    (hS Q l hlS' δ hδ0 hδ1 lam hl0 hl1 P K hGMP)
  refine ⟨(Regeneration.measurable_cycleRecord hd lam l k).aemeasurable,
    (Regeneration.measurable_cycleRecord hd lam l 0).aemeasurable, ?_⟩
  intro Φ hΦ _
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact (hren j).2 Φ hΦ

/-- The exact occupation statement after proving the slice identity. The
slice premise is internal and remains unproved from the frozen inputs. -/
theorem occupationStatement_of_slice_factor_and_frozen_inputs
    (hSlice : FirstRegenerationSliceFactorInput) (hE : GMPCouplingExistsV2Input)
    (hTail : GMPCouplingTailsV2Input) (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hFam : External.GMPReducedFamilyExistence)
    (hLoc : External.GMPKernelLocality) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀ :=
  occupationStatement_of_renewal_and_frozen_inputs
    (renewalLemma31Input_of_slice_factor_and_tails hSlice hTail) hE hTail hGir hInv hFam hLoc


end EinsteinRelation
