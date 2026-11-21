import EinsteinFull.Calculus.SbxAOriginalScopeSourceR08
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS1SplitGridFreshBits
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS2FutureKernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5Independence
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS8FutureKernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3ActualPastKernel
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3CleanQuenchedStoppedTube
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.PhysicalRegeneration.Calculus.C14S3BurnContraction
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanActualCovariance
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanHistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanScopeHelpers
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3CleanBurnPast
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3HistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Calculus.C2S3BurnPastLocality
import EinsteinFull.PhysicalRegeneration.Calculus.C2S3PastAssembly
import EinsteinFull.PhysicalRegeneration.Calculus.C6S3OneScaleCouplingFactory
import EinsteinFull.PhysicalRegeneration.Calculus.C6S3SuppliedPathRecenter
import EinsteinFull.PhysicalRegeneration.Calculus.C7S3CleanScopeAssembly
import EinsteinFull.PhysicalRegeneration.Calculus.C9FutureKernelIndicatorLocality
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAMinorizationWitnessTransferR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxASmoothScopeAssemblerR06
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1AllScaleTrialR02
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxTakeoverFutureKernelAssemblerR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxTakeoverFutureKernelReductionR01
import EinsteinFull.PhysicalRegeneration.Calculus.SunaS2RationalStoppedLaw
import EinsteinFull.PhysicalRegeneration.Calculus.SunaS2SuppliedStoppedLocality
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledHistoryHalfSpaceLocality
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxAOriginalScopeSourceR08`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
/-- The physical-kernel version of
`EinsteinFull.Blueprint.s1_original_scope_of_setwise_lower_and_tube`. -/
theorem s1_original_scope_of_setwise_lower_and_tube_phys
    (htails : node_app_u3A_regen_u2D_tailsStmt_phys)
    (hsetwise : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ),
      ∀ l : ℝ, 1 ≤ l → ∃ c : ℝ, 0 < c ∧
      ∀ (Q : EnvironmentLaw d Λ r),
      ∀ (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ h0.le h1 P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal (c * μ ^ d) •
              (volume : Measure (Vec d)).restrict
                (endpointBall (Renewal.forceCoord hd) (l / μ) x) ≤
            ((P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (l / μ) x}).map
                (fun γ => γ (Renewal.regenDelta μ)))
    (hTube : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀),
      ∀ (lam : ℝ) (h0 : 0 < |lam|) (h1 : |lam| ≤ 1),
        ∃ P : QuenchedPathLaws d,
          EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q |lam| h0.le h1 P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal ε ≤ P (x, ω)
              {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta |lam|),
                euclideanNorm (γ s - x) ≤ (l / |lam|) / 2}) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys := by
  have hminor : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ L : ℝ), 1 ≤ L →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1)
        (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω))
          (Renewal.regenDelta μ) δ (L / μ) (Renewal.forceCoord hd) := by
    intro d hd Λ₀ r₀ L hL
    obtain ⟨c, hc, hbound⟩ := hsetwise d hd Λ₀ r₀ L hL
    obtain ⟨hδ0, hδ1, hdom⟩ :=
      SbxASourceSetwiseDensityR05.source_minorization_of_rescaled_setwise
        (Renewal.forceCoord hd) L c (lt_of_lt_of_le zero_lt_one hL) hc
    refine ⟨SbxS14MinorizationVolumeR03.windowCoinCoefficient (Renewal.forceCoord hd) L c,
      hδ0, hδ1, ?_⟩
    intro Q μ h0 h1 P hP
    obtain ⟨P', hP', hPbound⟩ := hbound Q μ h0 h1
    have hm : ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P' (x, ω))
        (Renewal.regenDelta μ)
        (SbxS14MinorizationVolumeR03.windowCoinCoefficient (Renewal.forceCoord hd) L c)
        (L / μ) (Renewal.forceCoord hd) := by
      filter_upwards [hPbound] with ω hω
      exact hdom μ h0 (Renewal.regenDelta μ) (fun x => P' (x, ω)) hω
    exact source_minorization_transfer_supplied_kernel_phys hd Q μ h0.le h1 P' P hP' hP
      _ _ _ _ hm
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  obtain ⟨L₀, hL₀, _, htail⟩ := htails d hd Λ₀ r₀
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h0
  have hall : ∀ n : ℕ, ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      ∃ t : ℝ≥0, (n : ℝ) < q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
    intro n
    let L : ℝ := max L₀ 1 + ((n : ℝ) + 1) * lam
    have hL1 : 1 ≤ L := by
      dsimp [L]
      have hp : 0 ≤ ((n : ℝ) + 1) * lam := mul_nonneg (by positivity) h0.le
      linarith [le_max_right L₀ 1]
    have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    have hLge : L₀ ≤ L := by
      dsimp [L]
      have hp : 0 ≤ ((n : ℝ) + 1) * lam := mul_nonneg (by positivity) h0.le
      linarith [le_max_left L₀ 1]
    have hn : (n : ℝ) < 2 * (L / lam) := by
      have hb : (n : ℝ) + 1 ≤ L / lam := by
        apply (le_div_iff₀ h0).2
        dsimp [L]
        linarith [le_max_left L₀ 1]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨δ', hδ0', hδ1', hmin⟩ := hminor d hd Λ₀ r₀ L hL1
    obtain ⟨P', _, hP', hMarkov, hstart, hmin'⟩ :=
      SbxS1CouplingAssemblyR02.patch_reduced_kernel_phys hd Q lam h0.le h1
        (Renewal.regenDelta lam) δ' (L / lam) (Renewal.forceCoord hd) P hK.2.2.1
        (hmin Q lam h0 h1 P hK.2.2.1)
    let : IsMarkovKernel P' := hMarkov
    have hR : 0 < L / lam := div_pos hL h0
    let K' := EinsteinFull.Regeneration.splitContinuousCouplingKernel
      (Renewal.regenDelta lam) hΔ δ' (L / lam) (Renewal.forceCoord hd) hδ0' hδ1' hR P' hmin'
    have hK' : IsRegenerationCouplingPhys hd Q lam L δ' h0.le h1 P' K' :=
      EinsteinFull.Regeneration.s1_canonical_all_clauses_phys (Renewal.regenDelta lam) hΔ δ'
        (L / lam) (Renewal.forceCoord hd) hδ0' hδ1' hR P' hmin' hstart hd Q h0.le h1 hP'
    obtain ⟨c, C, a, M, hc, _, _, _, _, htail'⟩ := htail L hLge δ' hδ0' hδ1'
    obtain ⟨_, _, ht, _, _⟩ := htail' Q lam h0 h1 P' K' hK'
    have ht' : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam)
        lam (L / lam) c C (Renewal.forceCoord hd) K' := by
      intro t ht0
      simpa only [EinsteinFull.regenerationTime, Regeneration.regenerationTime_one] using ht t ht0
    have hfin := firstRegenerationTime_ne_top_ae_of_tail Q.measure K'
      (Renewal.regenDelta lam) lam (L / lam) c C hc h0 (Renewal.forceCoord hd) ht'
    have hev : ∀ᵐ q ∂annealedCoupledLaw Q.measure K',
        q.2.1 ∈ {γ : Path d | ∃ t : ℝ≥0, (n : ℝ) < γ t (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd)} := by
      filter_upwards [hfin] with q hq
      obtain ⟨t, ht0⟩ := c1_s3_excursion_of_finite_first_regeneration
        (Renewal.regenDelta lam) hΔ lam (L / lam) h0 hR q.2 (Renewal.forceCoord hd) hq
      exact ⟨t, hn.trans_le ht0⟩
    exact s1_transfer_supplied_path_event_phys hd Q lam h0.le h1 P' P K' K
      hK'.2.2.1 hK.2.2.1 hK'.1 hK.1 hK'.2.1 hK.2.1 _
      (c19_s3_measurableSet_excursion _ _) hev
  have hunbounded : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
    filter_upwards [ae_all_iff.mpr hall] with q hq
    intro B
    obtain ⟨n, hn⟩ := exists_nat_gt B
    obtain ⟨t, ht⟩ := hq n
    exact ⟨t, le_of_lt (hn.trans ht)⟩
  obtain ⟨ε, hε, hε1, hbound⟩ := hTube d hd Λ₀ r₀ l hl
  have habs : |lam| = lam := abs_of_pos h0
  obtain ⟨P', hP', htube⟩ := hbound Q lam (by simpa only [habs] using h0)
    (by simpa only [habs] using h1)
  have hP'' : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0.le h1 P' := by
    simpa only [habs] using hP'
  have htube' : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal ε ≤ P' (x, ω)
        {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - x) ≤ (l / lam) / 2} := by
    simpa only [habs] using htube
  have htubeP := s1_transfer_uniform_quenched_path_lower_bound_phys hd Q lam h0.le h1 P P'
    hK.2.2.1 hP'' (fun x => {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
      euclideanNorm (γ s - x) ≤ (l / lam) / 2}) (ENNReal.ofReal ε) htube'
  let μ := annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hguard : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}) := by
    intro m A hA N
    have ht := c10_clean_stopped_tube_of_uniform_quenched_tube_phys hd Q lam h0 h1 l δ
      P K hK (by
        intro ω hω r x a N
        exact c10_regeneration_guard_prefix_restart hd ω lam
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          hω h0 h1 r l a hl N x) ε hε htubeP m A hA N
    have hg := c10_clean_coupling_scope_guard_estimate_of_tube_estimate μ
      (Renewal.regenDelta lam) hΔ lam (l / lam) ε A m (Renewal.forceCoord hd) N ht
    simpa only [c10CleanCouplingScopeEvenGuardFailure, c10CleanCouplingScopePassage,
      c10CleanCouplingScopeEvenGuard, couplingScopeEvenGuardFailure, couplingScopePassage,
      couplingScopeEvenGuard] using hg
  exact s1_smooth_scope_of_guard_and_future_kernel_phys
    node_app_u3A_factorization_u23_future_u2D_kernel_of_deps_phys hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hunbounded ε hε hε1 hguard hD

end EinsteinFull.Blueprint
