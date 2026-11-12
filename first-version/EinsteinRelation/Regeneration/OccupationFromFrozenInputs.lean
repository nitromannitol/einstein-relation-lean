import EinsteinRelation.Regeneration.FirstRewardFromGirsanov
import EinsteinRelation.Entropy.ResolventFromWeak
import EinsteinRelation.Diffusion.RealizationUniquenessFromLocality

/-! # Occupation bounds conditional on the internal renewal lemma

Source `paper/main.tex:348–354,445–517`. This implication has exactly the
`Entropy.OccupationStatement` conclusion. The Girsanov step is derived from its
frozen endpoint, invariance, reduced-family and tail inputs. Path-law uniqueness
is derived from the frozen locality input. Lemma 3.1 remains an explicit internal
premise, separate from the cited external inputs.
-/

namespace EinsteinRelation

/-- Proposition 3.2 from Lemma 3.1 and the frozen external contracts
(`paper/main.tex:348–354,445–517`). The renewal premise is the paper's own
lemma, not an additional external input. -/
theorem occupationStatement_of_renewal_and_frozen_inputs
    (hR : RenewalLemma31Input) (hE : GMPCouplingExistsV2Input)
    (hTail : GMPCouplingTailsV2Input) (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hFam : External.GMPReducedFamilyExistence)
    (hLoc : External.GMPKernelLocality) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀ := by
  intro d hd Λ₀ r₀ hΛ₀ hr₀
  have hS := firstRewardStepFrozen_of_girsanov hGir hInv hFam hTail
  have hU : RealizationPathLawUniqueInput := Diffusion.realization_pathLaw_eq_of_locality hLoc
  obtain ⟨l₀, hl₀, hocc⟩ := occupationTwin_of_steps hR hE hTail hS hU d hd Λ₀ r₀ hΛ₀ hr₀
  refine ⟨l₀, hl₀, fun l hl => ?_⟩
  obtain ⟨p₀, hp₀, hp⟩ := hocc l hl
  refine ⟨p₀, hp₀, fun p hpp => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hp p hpp
  refine ⟨C, hC, ?_⟩
  intro Q lam hl0 hl1 IQ P hP hIQ
  obtain ⟨rfl, hGMP⟩ := hIQ
  exact hbound Q lam hl0 hl1 P hP hGMP


end EinsteinRelation
