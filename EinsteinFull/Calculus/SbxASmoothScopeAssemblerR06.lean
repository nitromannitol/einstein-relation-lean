import EinsteinFull.Calculus.SbxS1ScopeAssemblyR03
import EinsteinFull.Blueprint.Foundation.Draft.SbxCFactorizationSmoothR01

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint

theorem s1_smooth_all_cycles_of_guard_and_endpoint
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
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
theorem s1_smooth_scope_of_guard_and_endpoint
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
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
  have hfinite := s1_smooth_all_cycles_of_guard_and_endpoint hd Q
    lam h0 h1 l δ hl hδ0 hδ1 P K hK hunbounded ε hε hε1 hguard η hη hη1 hendpoint
  intro k
  refine ⟨(c19_clean_coupling_scope_measurable hd lam l k).1,
    (c19_clean_coupling_scope_measurable hd lam l k).2, ?_⟩
  intro ρ hρ
  apply (c19_clean_coupling_scope_ae_finite_iff_grid_record hd lam l h0 hl k ρ).mp
  apply (c19_clean_coupling_scope_both_laws_finite_iff hd Q lam l K hK.1 hD k).mpr
    (hfinite.mono fun q hq => hq k) ρ hρ

/-- The actual past kernel and the future-kernel input supply endpoint success. -/
theorem s1_smooth_scope_of_guard_and_future_kernel
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
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
  apply s1_smooth_scope_of_guard_and_endpoint hd Q lam h0 h1 l δ
    hl hδ0 hδ1 P K hK hunbounded ε hε hε1 hguard η hη hη1 ?_ hD
  intro m J N k
  exact c7_clean_burn_endpoint_of_local_past hFuture hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK hcov m k _
    (c1_s3_measurableSet_trial_burn_prebridge _ _ _ _ _ _ _ _) η hmean (hpast m J N k)


/-- Conditional assembly on smooth laws. The two displayed analytic estimates
are source minorization and centered tube survival; neither is proved here. -/
theorem s1_smooth_scope_of_minorization_and_one_kernel_tube
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hminor : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∀ L : ℝ, 1 ≤ L → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
        ∀ (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d),
        IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P →
        ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω))
          (Renewal.regenDelta lam) δ (L / lam) (Renewal.forceCoord hd))
    (hTube : ∀ {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d) (l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
          ∀ (lam : ℝ) (h0 : 0 < |lam|) (h1 : |lam| ≤ 1),
          ∃ P : QuenchedPathLaws d,
            IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| h0.le h1 P ∧
            ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
              ENNReal.ofReal ε ≤ P (x, ω)
                {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta |lam|),
                  euclideanNorm (γ s - x) ≤ (l / |lam|) / 2}) :
    SbxCFactorizationR01.couplingScopeSmoothStmt := by
  intro d hd D Q hQ lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  obtain ⟨L₀, hL₀, _, htail⟩ := htails d hd D.ellipticity D.dependenceRange
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
    obtain ⟨δ', hδ0', hδ1', hmin⟩ := hminor d hd D L hL1
    obtain ⟨P', _, hP', hMarkov, hstart, hmin'⟩ :=
      SbxS1CouplingAssemblyR02.patch_reduced_kernel hd Q lam h0.le h1
        (Renewal.regenDelta lam) δ' (L / lam) (Renewal.forceCoord hd) P hK.2.2.1
        (hmin Q hQ lam h0 h1 P hK.2.2.1)
    letI : IsMarkovKernel P' := hMarkov
    have hR : 0 < L / lam := div_pos hL h0
    let K' := EinsteinFull.Regeneration.splitContinuousCouplingKernel
      (Renewal.regenDelta lam) hΔ δ' (L / lam) (Renewal.forceCoord hd) hδ0' hδ1' hR P' hmin'
    have hK' : IsRegenerationCoupling hd Q lam L δ' h0.le h1 P' K' :=
      EinsteinFull.Regeneration.s1_canonical_all_clauses (Renewal.regenDelta lam) hΔ δ'
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
    exact s1_transfer_supplied_path_event hd Q lam h0.le h1 P' P K' K
      hK'.2.2.1 hK.2.2.1 hK'.1 hK.1 hK'.2.1 hK.2.1 _
      (c19_s3_measurableSet_excursion _ _) hev
  have hunbounded : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
    filter_upwards [ae_all_iff.mpr hall] with q hq
    intro B
    obtain ⟨n, hn⟩ := exists_nat_gt B
    obtain ⟨t, ht⟩ := hq n
    exact ⟨t, le_of_lt (hn.trans ht)⟩
  obtain ⟨ε, hε, hε1, hbound⟩ := hTube hd D l hl
  have habs : |lam| = lam := abs_of_pos h0
  obtain ⟨P', hP', htube⟩ := hbound Q hQ lam (by simpa only [habs] using h0)
    (by simpa only [habs] using h1)
  have hP'' : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P' := by
    simpa only [habs] using hP'
  have htube' : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal ε ≤ P' (x, ω)
        {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - x) ≤ (l / lam) / 2} := by
    simpa only [habs] using htube
  have htubeP := s1_transfer_uniform_quenched_path_lower_bound hd Q lam h0.le h1 P P'
    hK.2.2.1 hP'' (fun x => {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
      euclideanNorm (γ s - x) ≤ (l / lam) / 2}) (ENNReal.ofReal ε) htube'
  let μ := annealedCoupledLaw Q.measure K
  letI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hguard : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}) := by
    intro m A hA N
    have ht := c10_clean_stopped_tube_of_uniform_quenched_tube hd Q lam h0 h1 l δ
      P K hK (by
        intro ω hω r x a N
        exact c10_regeneration_guard_prefix_restart hd (zeroPotentialReducedPair ω) lam
          (sourceReducedBound D.ellipticity) (one_le_sourceReducedBound Q.ellipticity_parameter)
          hω h0 h1 r l a hl N x) ε hε htubeP m A hA N
    have hg := c10_clean_coupling_scope_guard_estimate_of_tube_estimate μ
      (Renewal.regenDelta lam) hΔ lam (l / lam) ε A m (Renewal.forceCoord hd) N ht
    simpa only [c10CleanCouplingScopeEvenGuardFailure, c10CleanCouplingScopePassage,
      c10CleanCouplingScopeEvenGuard, couplingScopeEvenGuardFailure, couplingScopePassage,
      couplingScopeEvenGuard] using hg
  exact s1_smooth_scope_of_guard_and_future_kernel
    node_app_u3A_factorization_u23_future_u2D_kernel_of_deps hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK hunbounded ε hε hε1 hguard hD

end EinsteinFull.Blueprint
