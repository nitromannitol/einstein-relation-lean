import EinsteinFull.Calculus.SbxASmoothScopeAssemblerR06
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
`EinsteinFull.Calculus.SbxASmoothScopeAssemblerR06`

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
theorem s1_smooth_all_cycles_of_guard_and_endpoint_phys
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hunbounded : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hguard : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q.measure K
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hendpoint : ∀ m J N k : ℕ,
      let Δ := Renewal.regenDelta lam
      let R := l / lam
      let i := Renewal.forceCoord hd
      let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
      η * (∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂K (0, ω) ∂Q.measure) ≤
        ∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z *
          endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
            (fun y => ∫ w, killedFutureTest R i (fun _ => 1)
              ((y, ω), w) ∂K (y, ω)) ∂K (0, ω) ∂Q.measure) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ k : ℕ, regenerationTime hd lam l k q.2 ≠ ⊤ := by
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h0
  have hpass : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (s : ℝ≥0) (a : ℝ) (n : ℕ),
      passageSequence (Renewal.regenDelta lam) lam (l / lam) a
        (pathTimeShift q.2.1 s) (Renewal.forceCoord hd) n ≠ ⊤ := by
    filter_upwards [hunbounded] with q hq s a n
    exact c2_s3_shifted_passages_finite_of_unbounded _ _ _ _ _ hq s a n
  have hentry := c14_s3_entries_of_finite_passages_and_guards Q.measure K hK.1
    (Renewal.regenDelta lam) hΔ δ hδ0 hδ1.le hK.2.2.2.1 lam (l / lam) h0
    (div_pos hl h0) (Renewal.forceCoord hd) hpass ε hε hε1 hguard
  obtain ⟨η', hη', hprebridge⟩ := c14_s3_uniform_prebridge_win_of_iterated_endpoint_phys
    hd Q lam h0 h1 l δ hl hδ0.le P K hK η hη hη1 hendpoint
  obtain ⟨η'', hη'', hstep⟩ := c14_s3_uniform_burn_contraction_of_integrated_prebridge
    Q.measure K hK.1 _ hΔ δ hδ0.le hK.2.2.2.1 lam (l / lam) h0 (div_pos hl h0)
    (Renewal.forceCoord hd) (fun m => hentry.mono fun q hq => (hq m).2)
    η' hη' hprebridge.1 hprebridge.2
  exact c7_s3_all_cycles_finite_of_unbounded_and_guard_contraction hd Q.measure K hK.1
    lam l h0 hl δ hδ0 hδ1.le hK.2.2.2.1 hunbounded ε hε hε1 hguard η'' hη'' hstep

attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
/-- The physical-kernel version of
`EinsteinFull.Blueprint.s1_smooth_scope_of_guard_and_endpoint`. -/
theorem s1_smooth_scope_of_guard_and_endpoint_phys
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hunbounded : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hguard : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q.measure K
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hendpoint : ∀ m J N k : ℕ,
      let Δ := Renewal.regenDelta lam
      let R := l / lam
      let i := Renewal.forceCoord hd
      let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
      η * (∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂K (0, ω) ∂Q.measure) ≤
        ∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z *
          endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
            (fun y => ∫ w, killedFutureTest R i (fun _ => 1)
              ((y, ω), w) ∂K (y, ω)) ∂K (0, ω) ∂Q.measure)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) :
    ∀ k : ℕ, Measurable (regenerationTime hd lam l k) ∧
      Measurable (regenerationRecord hd lam l k) ∧
      ∀ ρ ∈ ({annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × CoupledSample d))),
        ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * k ≤ n ∧
          regenerationTime hd lam l k q.2 =
            (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
          regenerationRecord hd lam l k q =
            futureRecord (Renewal.regenDelta lam) (l / lam) q.1 q.2
              (Renewal.forceCoord hd) ((n : ℝ≥0) * Renewal.regenDelta lam) := by
  have hfinite := s1_smooth_all_cycles_of_guard_and_endpoint_phys hd Q
    lam h0 h1 l δ hl hδ0 hδ1 P K hK hunbounded ε hε hε1 hguard η hη hη1 hendpoint
  intro k
  refine ⟨(c19_clean_coupling_scope_measurable hd lam l k).1,
    (c19_clean_coupling_scope_measurable hd lam l k).2, ?_⟩
  intro ρ hρ
  apply (c19_clean_coupling_scope_ae_finite_iff_grid_record hd lam l h0 hl k ρ).mp
  apply (c19_clean_coupling_scope_both_laws_finite_iff hd Q lam l K hK.1 hD k).mpr
    (hfinite.mono fun q hq => hq k) ρ hρ

/-- The physical-kernel version of
`EinsteinFull.Blueprint.s1_smooth_scope_of_guard_and_future_kernel`. -/
theorem s1_smooth_scope_of_guard_and_future_kernel_phys
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hunbounded : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hguard : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q.measure K
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}))
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) :
    ∀ k : ℕ, Measurable (regenerationTime hd lam l k) ∧
      Measurable (regenerationRecord hd lam l k) ∧
      ∀ ρ ∈ ({annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × CoupledSample d))),
        ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * k ≤ n ∧
          regenerationTime hd lam l k q.2 =
            (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ∧
          regenerationRecord hd lam l k q =
            futureRecord (Renewal.regenDelta lam) (l / lam) q.1 q.2
              (Renewal.forceCoord hd) ((n : ℝ≥0) * Renewal.regenDelta lam) := by
  let := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let η := (annealedCoupledLaw Q.measure K).real (regenerationNoReturn hd (l / lam))
  have hη : 0 < η := ENNReal.toReal_pos hD (measure_ne_top _ _)
  have hη1 : η ≤ 1 := measureReal_le_one
  have hcov := c19_clean_actual_coupled_covariance_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
  obtain ⟨_, _, _, _, _, hpast⟩ :=
    c1_s3_clean_burn_past_of_literal_past_kernel_phys EinsteinFull.c10_actual_past_kernel_phys
      hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  have hmean : ∀ᵐ y ∂(volume : Measure (Vec d)), η ≤ ∫ ω,
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) ∂Q.measure := by
    filter_upwards [c19_clean_actual_killed_future_one_mean_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK] with y hy
    exact le_of_eq hy.symm
  apply s1_smooth_scope_of_guard_and_endpoint_phys hd Q lam h0 h1 l δ
    hl hδ0 hδ1 P K hK hunbounded ε hε hε1 hguard η hη hη1 ?_ hD
  intro m J N k
  exact c7_clean_burn_endpoint_of_local_past_phys hFuture hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hcov m k _
    (c1_s3_measurableSet_trial_burn_prebridge _ _ _ _ _ _ _ _) η hmean (hpast m J N k)

end EinsteinFull.Blueprint
