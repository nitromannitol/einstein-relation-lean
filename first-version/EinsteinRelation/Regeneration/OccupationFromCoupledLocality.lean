import EinsteinRelation.Regeneration.KilledJointFutureLocality
import EinsteinRelation.Regeneration.SliceFactorFromHalfSpaceLocality
import EinsteinRelation.Regeneration.OccupationFromSliceFactor

/-!
# Renewal and occupation after the coupled locality construction

Source `paper/main.tex:348–444,445–517`. All slice calculations,
normalization, conditional invariance and iteration are proved below
the explicit internal coupled-locality obligation. That obligation still
requires a proof from the one-interval construction and frozen GMP inputs;
it is not an authorized external input.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation

/-- The remaining internal kernel construction in Step 2 and the spatial
covariance used in Step 3 (`paper/main.tex:383–408`). This proposition is
not a literature input and has no proof in this module. -/
def CoupledKernelLocalityInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    ∀ (lam l δ : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1), 0 < l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
        Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ
          hl0.le hl1 P K →
        Regeneration.HasPastHalfSpaceVersions Q.measure (Regeneration.Renewal.regenDelta lam)
            (Regeneration.Renewal.forceCoord hd) (l / lam) K ∧
          Regeneration.HasKilledPathBitFutureVersions Q.measure
            (Regeneration.Renewal.forceCoord hd) (l / lam) K ∧
          ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
            (K xω).map (Regeneration.recenterSample xω.1) = K (0, translate xω.1 xω.2)

/-- The precise Lemma 3.1 production target follows once the remaining
coupled locality and covariance construction is supplied. Only the frozen
tail is otherwise assumed; the source's renewal proof is carried out. -/
theorem renewalLemma31Input_of_coupled_locality_and_tails
    (hLocal : CoupledKernelLocalityInput) (hTail : GMPCouplingTailsV2Input) :
    RenewalLemma31Input := by
  intro d hd Λ₀ r₀
  obtain ⟨lT, hlT, hT⟩ := hTail d hd Λ₀ r₀
  refine ⟨max lT 1, lt_of_lt_of_le hlT (by gcongr; exact le_max_left _ _), ?_⟩
  intro Q l hl δ hδ0 hδ1 lam hl0 hl1 P K hGMP hD k hk
  have hlT' : lT ≤ l := (le_max_left _ _).trans hl
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hl)
  have hR : 0 < l / lam := div_pos hlpos hl0
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam := regenDelta_pos hl0
  have hlR : l ≤ l / lam := (le_div_iff₀ hl0).mpr (by nlinarith)
  have hgap : r₀ < 2 * (l / lam) :=
    lt_of_lt_of_le hlT (by nlinarith)
  obtain ⟨c, C, hc, htail⟩ := hT l hlT' δ hδ0 hδ1
  have hfin := Regeneration.firstRegenerationTime_ne_top_ae_of_tail Q.measure K
    (Regeneration.Renewal.regenDelta lam) lam (l / lam) c C hc hl0
    (Regeneration.Renewal.forceCoord hd) (htail lam hl0 hl1 Q P K hGMP).2
  obtain ⟨hpast, hkilled, hcov⟩ := hLocal d hd Λ₀ r₀ Q lam l δ hl0 hl1 hlpos hδ0 hδ1 P K hGMP
  have hSlice := Regeneration.firstRegenerationSliceFactor_of_halfSpace_locality hd Q lam hl0 hl1
    P K hGMP.1 hGMP.2.1 hGMP.2.2.1 (Regeneration.Renewal.regenDelta lam) hΔ δ (l / lam) hR
    (Regeneration.Renewal.forceCoord hd) hgap hGMP.2.2.2.2.1 hGMP.2.2.2.2.2.2.1 hpast hcov
    (Regeneration.killedJointFutureLocality_of_killedPathBitVersions Q.measure K hGMP.1
      (l / lam) (Regeneration.Renewal.forceCoord hd) hkilled) hD
  have hren := Regeneration.renewal_marginals_of_slice_factor Q.measure K hGMP.1
    (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) hl0 hR
    (Regeneration.Renewal.forceCoord hd) hGMP.2.2.2.2.2.1 hfin hD hSlice
  refine ⟨(Regeneration.measurable_cycleRecord hd lam l k).aemeasurable,
    (Regeneration.measurable_cycleRecord hd lam l 0).aemeasurable, ?_⟩
  intro Φ hΦ _
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact (hren j).2 Φ hΦ

/-- The exact occupation conclusion, conditional on the listed frozen
external inputs and the still-unproved internal coupled-locality input. -/
theorem occupationStatement_of_coupled_locality_and_frozen_inputs
    (hLocal : CoupledKernelLocalityInput) (hE : GMPCouplingExistsV2Input)
    (hTail : GMPCouplingTailsV2Input) (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hFam : External.GMPReducedFamilyExistence)
    (hLoc : External.GMPKernelLocality) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀ :=
  occupationStatement_of_renewal_and_frozen_inputs
    (renewalLemma31Input_of_coupled_locality_and_tails hLocal hTail) hE hTail hGir hInv hFam hLoc


end EinsteinRelation
