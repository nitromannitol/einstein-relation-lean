import EinsteinFull.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.Calculus.C7S3CleanAllCycleAssembly
import EinsteinFull.Calculus.C19S3CleanScopeHelpers
import EinsteinFull.Calculus.C10S3CleanQuenchedStoppedTube
import EinsteinFull.Calculus.C10S3SuppliedPositiveRadiusRestart

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- Path events transfer between actual couplings even when their supplied
reduced kernels are presented by different jointly measurable kernels. -/
theorem s1_transfer_supplied_path_event {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P P' : QuenchedPathLaws d) (K K' : CoupledQuenchedLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (hP' : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P')
    (hK : HasProbabilityLaws Q.measure K) (hK' : HasProbabilityLaws Q.measure K')
    (hM : HasPathMarginals Q.measure K P) (hM' : HasPathMarginals Q.measure K' P')
    (A : Set (Path d)) (hA : MeasurableSet A)
    (h : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, q.2.1 ∈ A) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K', q.2.1 ∈ A := by
  have heq := EinsteinFull.s6_supplied_reduced_kernel_pathLaw_unique hd Q lam h0 h1 P P' hP hP'
  have hf := ae_quenched_of_annealed Q.measure K hK h
  have hp : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂P' (0, ω), x ∈ A := by
    filter_upwards [hf, hM.1, heq] with ω hfω hmap he
    rw [← he 0, ← hmap]
    exact (ae_map_iff measurable_fst.aemeasurable hA).2 hfω
  apply Measure.ae_compProd_of_ae_ae (hA.preimage measurable_snd.fst)
  filter_upwards [hp, hK'.1, hM'.1] with ω hpω hprob hmap
  let : IsProbabilityMeasure (originCoupledLaw K' ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K') ω]
  apply ae_of_ae_map measurable_fst.aemeasurable
  change ∀ᵐ y ∂(K' (0, ω)).map Prod.fst, y ∈ A
  rwa [hmap]

/-- A uniform quenched path estimate for one reduced kernel transfers to every
supplied reduced kernel, on a single conull set of environments and for every
starting point. The events may depend on the starting point. -/
theorem s1_transfer_uniform_quenched_path_lower_bound {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P P' : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (hP' : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P')
    (A : Vec d → Set (Path d)) (ε : ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ε ≤ P' (x, ω) (A x)) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ε ≤ P (x, ω) (A x) := by
  filter_upwards [EinsteinFull.s6_supplied_reduced_kernel_pathLaw_unique
    hd Q lam h0 h1 P P' hP hP', hbound] with ω heq hω
  intro x
  rw [heq x]
  exact hω x

/-- The full-range conditional coupling construction and the tail estimate
imply arbitrarily large excursions for every supplied actual coupling. -/
theorem s1_supplied_unbounded_of_uniform_source_minorization
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hminor : SbxS1CouplingAssemblyR02.UniformSourceMinorization)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
  obtain ⟨L₀, hL₀, _, htail⟩ := htails d hd Λ₀ r₀
  obtain ⟨L₁, hL₁, _, hfull⟩ :=
    SbxS1CouplingAssemblyR02.full_range_coupling_nonreturn_of_uniform_source_minorization
      htails hminor d hd Λ₀ r₀
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h0
  have hall : ∀ n : ℕ, ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      ∃ t : ℝ≥0, (n : ℝ) < q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
    intro n
    let L : ℝ := max L₀ L₁ + ((n : ℝ) + 1) * lam
    have hL : 0 < L := by dsimp [L]; positivity
    have hLge : L₀ ≤ L := by
      dsimp [L]
      have hp : 0 ≤ ((n : ℝ) + 1) * lam := mul_nonneg (by positivity) h0.le
      linarith [le_max_left L₀ L₁]
    have hLge' : L₁ ≤ L := by
      dsimp [L]
      have hp : 0 ≤ ((n : ℝ) + 1) * lam := mul_nonneg (by positivity) h0.le
      linarith [le_max_right L₀ L₁]
    have hn : (n : ℝ) < 2 * (L / lam) := by
      have hb : (n : ℝ) + 1 ≤ L / lam := by
        apply (le_div_iff₀ h0).2
        dsimp [L]
        linarith [le_max_left L₀ L₁]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨δ', hδ0, hδ1, hc⟩ := hfull L hLge'
    obtain ⟨P', K', hK', _⟩ := hc Q lam h0 h1
    obtain ⟨c, C, a, M, hc, _, _, _, _, htail'⟩ := htail L hLge δ' hδ0 hδ1
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
        (Renewal.regenDelta lam) hΔ lam (L / lam) h0 (div_pos hL h0) q.2
        (Renewal.forceCoord hd) hq
      exact ⟨t, hn.trans_le ht0⟩
    exact s1_transfer_supplied_path_event hd Q lam h0.le h1 P' P K' K
      hK'.2.2.1 hK.2.2.1 hK'.1 hK.1 hK'.2.1 hK.2.1 _
      (c19_s3_measurableSet_excursion _ _) hev
  filter_upwards [ae_all_iff.mpr hall] with q hq
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  obtain ⟨t, ht⟩ := hq n
  exact ⟨t, le_of_lt (hn.trans ht)⟩

/-- Finite trials for the supplied coupling follow from the literal guard and
endpoint success estimates. The deterministic restart, fresh coins, passage
entries and contraction are obtained from the actual coupling clauses. -/
theorem s1_supplied_all_cycles_of_guard_and_endpoint
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hminor : SbxS1CouplingAssemblyR02.UniformSourceMinorization)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
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
  have hunbounded := s1_supplied_unbounded_of_uniform_source_minorization
    htails hminor hd Q lam h0 h1 l δ P K hK
  have hpass : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (s : ℝ≥0) (a : ℝ) (n : ℕ),
      passageSequence (Renewal.regenDelta lam) lam (l / lam) a
        (pathTimeShift q.2.1 s) (Renewal.forceCoord hd) n ≠ ⊤ := by
    filter_upwards [hunbounded] with q hq s a n
    exact c2_s3_shifted_passages_finite_of_unbounded _ _ _ _ _ hq s a n
  have hentry := c14_s3_entries_of_finite_passages_and_guards Q.measure K hK.1
    (Renewal.regenDelta lam) hΔ δ hδ0 hδ1.le hK.2.2.2.1 lam (l / lam) h0
    (div_pos hl h0) (Renewal.forceCoord hd) hpass ε hε hε1 hguard
  obtain ⟨η', hη', hprebridge⟩ := c14_s3_uniform_prebridge_win_of_iterated_endpoint
    hd Q lam h0 h1 l δ hl hδ0.le P K hK η hη hη1 hendpoint
  obtain ⟨η'', hη'', hstep⟩ := c14_s3_uniform_burn_contraction_of_integrated_prebridge
    Q.measure K hK.1 _ hΔ δ hδ0.le hK.2.2.2.1 lam (l / lam) h0 (div_pos hl h0)
    (Renewal.forceCoord hd) (fun m => hentry.mono fun q hq => (hq m).2)
    η' hη' hprebridge.1 hprebridge.2
  exact c7_s3_all_cycles_finite_of_unbounded_and_guard_contraction hd Q.measure K hK.1
    lam l h0 hl δ hδ0 hδ1.le hK.2.2.2.1 hunbounded ε hε hε1 hguard η'' hη'' hstep

attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat

/-- Scope for the supplied coupling, conditional on the displayed trial estimates. -/
theorem s1_supplied_scope_of_guard_and_endpoint
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hminor : SbxS1CouplingAssemblyR02.UniformSourceMinorization)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
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
  have hfinite := s1_supplied_all_cycles_of_guard_and_endpoint htails hminor hd Q
    lam h0 h1 l δ hl hδ0 hδ1 P K hK ε hε hε1 hguard η hη hη1 hendpoint
  intro k
  refine ⟨(c19_clean_coupling_scope_measurable hd lam l k).1,
    (c19_clean_coupling_scope_measurable hd lam l k).2, ?_⟩
  intro ρ hρ
  apply (c19_clean_coupling_scope_ae_finite_iff_grid_record hd lam l h0 hl k ρ).mp
  apply (c19_clean_coupling_scope_both_laws_finite_iff hd Q lam l K hK.1 hD k).mpr
    (hfinite.mono fun q hq => hq k) ρ hρ

/-- The actual past kernel and the future-kernel input supply endpoint success. -/
theorem s1_supplied_scope_of_guard_and_future_kernel
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hminor : SbxS1CouplingAssemblyR02.UniformSourceMinorization)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
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
  letI := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let η := (annealedCoupledLaw Q.measure K).real (regenerationNoReturn hd (l / lam))
  have hη : 0 < η := ENNReal.toReal_pos hD (measure_ne_top _ _)
  have hη1 : η ≤ 1 := measureReal_le_one
  have hcov := c19_clean_actual_coupled_covariance hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
  obtain ⟨_, _, _, _, _, hpast⟩ :=
    c1_s3_clean_burn_past_of_literal_past_kernel EinsteinFull.c10_actual_past_kernel
      hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  have hmean : ∀ᵐ y ∂(volume : Measure (Vec d)), η ≤ ∫ ω,
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) ∂Q.measure := by
    filter_upwards [c19_clean_actual_killed_future_one_mean hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK] with y hy
    exact le_of_eq hy.symm
  apply s1_supplied_scope_of_guard_and_endpoint htails hminor hd Q lam h0 h1 l δ
    hl hδ0 hδ1 P K hK ε hε hε1 hguard η hη hη1 ?_ hD
  intro m J N k
  exact c7_clean_burn_endpoint_of_local_past hFuture hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hcov m k _
    (c1_s3_measurableSet_trial_burn_prebridge _ _ _ _ _ _ _ _) η hmean (hpast m J N k)

/-- Universal scope conditional on a guard estimate uniform in the law and force. -/
theorem s1_scope_of_uniform_guard_and_future_kernel
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hminor : SbxS1CouplingAssemblyR02.UniformSourceMinorization)
    (hguard : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
          (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
          (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
          (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K),
        ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q.measure K
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N})) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  obtain ⟨ε, hε, hε1, hbound⟩ := hguard hd Λ₀ r₀ l hl
  exact s1_supplied_scope_of_guard_and_future_kernel hFuture htails hminor hd Q lam
    h0 h1 l δ hl hsep hδ0 hδ1 P K hK ε hε hε1
    (hbound Q lam h0 h1 δ hδ0 hδ1 P K hK) hD

/-- Uniform quenched tube probabilities imply the literal uniform guard bound. -/
theorem s1_scope_of_uniform_quenched_tube_and_future_kernel
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hminor : SbxS1CouplingAssemblyR02.UniformSourceMinorization)
    (hTube : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
          (P : QuenchedPathLaws d),
          IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P →
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal ε ≤ P (x, ω)
              {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
                euclideanNorm (γ s - x) ≤ (l / lam) / 2}) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  apply s1_scope_of_uniform_guard_and_future_kernel hFuture htails hminor
  intro d hd Λ₀ r₀ l hl
  obtain ⟨ε, hε, hε1, htube⟩ := hTube hd Λ₀ r₀ l hl
  refine ⟨ε, hε, hε1, ?_⟩
  intro Q lam h0 h1 δ hδ0 hδ1 P K hK
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h0
  let μ := annealedCoupledLaw Q.measure K
  letI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  intro m A hA N
  have ht := c10_clean_stopped_tube_of_uniform_quenched_tube hd Q lam h0 h1 l δ
    P K hK (by
      intro ω hω r x a N
      exact c10_regeneration_guard_prefix_restart hd (zeroPotentialReducedPair ω) lam
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        hω h0 h1 r l a hl N x) ε hε (htube Q lam h0 h1 P hK.2.2.1) m A hA N
  have hg := c10_clean_coupling_scope_guard_estimate_of_tube_estimate μ
    (Renewal.regenDelta lam) hΔ lam (l / lam) ε A m (Renewal.forceCoord hd) N ht
  simpa only [c10CleanCouplingScopeEvenGuardFailure, c10CleanCouplingScopePassage,
    c10CleanCouplingScopeEvenGuard, couplingScopeEvenGuardFailure, couplingScopePassage,
    couplingScopeEvenGuard] using hg

end EinsteinFull.Blueprint
