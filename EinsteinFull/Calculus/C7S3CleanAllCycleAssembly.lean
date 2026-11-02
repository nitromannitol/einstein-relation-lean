import EinsteinFull.Calculus.C19S3CleanActualCovariance
import EinsteinFull.Calculus.C14S3BurnContraction
import EinsteinFull.Calculus.C19S3ExcursionsFromCofinalCouplings
import EinsteinFull.Calculus.C1S3FiniteRegenerationExcursion
import EinsteinFull.Calculus.C19S3CleanScopeHelpers
import EinsteinFull.Calculus.C7S3AllCyclesFromUnbounded
import EinsteinFull.Calculus.C7S3CleanScopeAssembly
import EinsteinFull.Calculus.C1S3CleanBurnEvent
import EinsteinFull.Calculus.C10S3CleanStoppedTube
import EinsteinFull.Calculus.C4S3CleanCofinalDensity
import EinsteinFull.Calculus.C1S3CleanBurnPast
import EinsteinFull.Calculus.C10S3ActualPastKernel
import EinsteinFull.Calculus.C4S3SelectedTubeAssembly

open MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration Classical

/-- A countable cofinal family of couplings yields unbounded excursions. -/
theorem c7_s3_unbounded_of_countable_cofinal_couplings
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hCofinal : ∀ L₀ : ℝ, ∃ L δ : ℕ → ℝ,
      (∀ n : ℕ, L₀ + (n : ℝ) ≤ L n ∧ 0 < L n ∧ 0 < δ n ∧ δ n < 1) ∧
      (∀ᵐ ω ∂Q.measure, ∀ n : ℕ, ∀ x : Vec d,
        ENNReal.ofReal (δ n) • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L n / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L n / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
      ∀ n, ∃ K : CoupledQuenchedLaws d,
        IsRegenerationCoupling hd Q lam (L n) (δ n) h0.le h1 P K)
    (l δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
  obtain ⟨L₀, hL₀, _, htail⟩ := htails d hd Λ₀ r₀
  obtain ⟨L, δs, hL, _, hKs⟩ := hCofinal L₀
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  have hall : ∀ n : ℕ, ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      ∃ t : ℝ≥0, (n : ℝ) < q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
    intro n
    obtain ⟨j, hj⟩ := exists_nat_gt (((n : ℝ) + 1) * lam)
    have hLpos : 0 < L j := (hL j).2.1
    have hLge : L₀ ≤ L j := by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith [(hL j).1]
    have hn : (n : ℝ) < 2 * (L j / lam) := by
      have hbound : (n : ℝ) + 1 ≤ L j / lam := by
        apply (le_div_iff₀ h0).2
        linarith [(hL j).1]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨K', hK'⟩ := hKs j
    have hδ'0 := (hL j).2.2.1
    have hδ'1 := (hL j).2.2.2
    obtain ⟨c, C, a, M, hc, _, _, _, _, htail'⟩ := htail (L j) hLge (δs j) hδ'0 hδ'1
    obtain ⟨_, _, htail'', _, _⟩ := htail' Q lam h0 h1 P K' hK'
    have ht : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam)
        lam (L j / lam) c C (Renewal.forceCoord hd) K' := by
      intro t ht
      simpa only [EinsteinFull.regenerationTime, Regeneration.regenerationTime_one] using htail'' t ht
    have hfin := firstRegenerationTime_ne_top_ae_of_tail Q.measure K'
      (Renewal.regenDelta lam) lam (L j / lam) c C hc h0 (Renewal.forceCoord hd) ht
    have hev : ∀ᵐ q ∂annealedCoupledLaw Q.measure K',
        q.2.1 ∈ {γ : Path d | ∃ t : ℝ≥0, (n : ℝ) < γ t (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd)} := by
      filter_upwards [hfin] with q hq
      obtain ⟨t, ht⟩ := c1_s3_excursion_of_finite_first_regeneration
        (Renewal.regenDelta lam) hΔ lam (L j / lam) h0 (div_pos hLpos h0) q.2
        (Renewal.forceCoord hd) hq
      exact ⟨t, hn.trans_le ht⟩
    exact c19_s3_transfer_path_event Q.measure P K' K hK'.1 hK.1
      hK'.2.1 hK.2.1 _ (c19_s3_measurableSet_excursion _ _) hev
  filter_upwards [ae_all_iff.mpr hall] with q hq
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  obtain ⟨t, ht⟩ := hq n
  exact ⟨t, le_of_lt (hn.trans ht)⟩

/-- A cofinal family, guard estimate and Burn contraction give finite cycles
for the supplied coupled law. -/
theorem c7_s3_all_cycles_of_countable_cofinal_and_guard
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hCofinal : ∀ L₀ : ℝ, ∃ L δ : ℕ → ℝ,
      (∀ n : ℕ, L₀ + (n : ℝ) ≤ L n ∧ 0 < L n ∧ 0 < δ n ∧ δ n < 1) ∧
      (∀ᵐ ω ∂Q.measure, ∀ n : ℕ, ∀ x : Vec d,
        ENNReal.ofReal (δ n) • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L n / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L n / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
      ∀ n, ∃ K : CoupledQuenchedLaws d,
        IsRegenerationCoupling hd Q lam (L n) (δ n) h0.le h1 P K)
    (l δ : ℝ) (hl : 0 < l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hwin : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q.measure K
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}))
    (η : ℝ) (hη : 0 < η)
    (hstep : ∀ m J N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q.measure K
      μ (couplingScopeTrialLost Δ lam (l / lam) m (Renewal.forceCoord hd) J (N + 1)) ≤
        ENNReal.ofReal (1 - η) * μ (couplingScopeTrialLost Δ lam (l / lam) m (Renewal.forceCoord hd) J N)) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ k : ℕ, regenerationTime hd lam l k q.2 ≠ ⊤ := by
  exact c7_s3_all_cycles_finite_of_unbounded_and_guard_contraction hd Q.measure K hK.1
    lam l h0 hl δ hδ0 hδ1.le hK.2.2.2.1
    (c7_s3_unbounded_of_countable_cofinal_couplings htails hd Q lam h0 h1 P hCofinal
      l δ hδ0 hδ1 K hK) ε hε hε1 hwin η hη hstep

/-- Endpoint averages, cofinal couplings, and the literal guard estimate imply all-cycle finiteness. -/
theorem c7_s3_all_cycles_of_countable_cofinal_and_endpoint
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hCofinal : ∀ L₀ : ℝ, ∃ L δ : ℕ → ℝ,
      (∀ n : ℕ, L₀ + (n : ℝ) ≤ L n ∧ 0 < L n ∧ 0 < δ n ∧ δ n < 1) ∧
      (∀ᵐ ω ∂Q.measure, ∀ n : ℕ, ∀ x : Vec d,
        ENNReal.ofReal (δ n) • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L n / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L n / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
      ∀ n, ∃ K : CoupledQuenchedLaws d,
        IsRegenerationCoupling hd Q lam (L n) (δ n) h0.le h1 P K)
    (l δ : ℝ) (hl : 0 < l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hwin : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q.measure K
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlower : ∀ m J N k : ℕ,
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
  have hunbounded := c7_s3_unbounded_of_countable_cofinal_couplings htails hd Q lam h0 h1 P
    hCofinal l δ hδ0 hδ1 K hK
  have hpass : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (s : ℝ≥0) (a : ℝ) (n : ℕ),
      passageSequence (Renewal.regenDelta lam) lam (l / lam) a
        (pathTimeShift q.2.1 s) (Renewal.forceCoord hd) n ≠ ⊤ := by
    filter_upwards [hunbounded] with q hq s a n
    exact c2_s3_shifted_passages_finite_of_unbounded _ _ _ _ _ hq s a n
  have hentry := c14_s3_entries_of_finite_passages_and_guards Q.measure K hK.1
    (Renewal.regenDelta lam) hΔ δ hδ0 hδ1.le hK.2.2.2.1 lam (l / lam) h0
    (div_pos hl h0) (Renewal.forceCoord hd) hpass ε hε hε1 hwin
  obtain ⟨η', hη', hprebridge⟩ := c14_s3_uniform_prebridge_win_of_iterated_endpoint
    hd Q lam h0 h1 l δ hl hδ0.le P K hK η hη hη1 hlower
  obtain ⟨η'', hη'', hstep⟩ := c14_s3_uniform_burn_contraction_of_integrated_prebridge
    Q.measure K hK.1 _ hΔ δ hδ0.le hK.2.2.2.1 lam (l / lam) h0 (div_pos hl h0)
    (Renewal.forceCoord hd) (fun m => hentry.mono fun q hq => (hq m).2)
    η' hη' hprebridge.1 hprebridge.2
  exact c7_s3_all_cycles_of_countable_cofinal_and_guard htails hd Q lam h0 h1 P
    hCofinal l δ hl hδ0 hδ1 K hK ε hε hε1 hwin η'' hη'' hstep

/-- Conditional scope assembly with literal cofinal, guard, covariance, mean and past inputs. -/
theorem c7_s3_clean_scope_of_cofinal_guard_local_past
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hCofinal : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
      (L₀ : ℝ), ∃ L δ : ℕ → ℝ,
        (∀ n : ℕ, L₀ + (n : ℝ) ≤ L n ∧ 0 < L n ∧ 0 < δ n ∧ δ n < 1) ∧
        (∀ᵐ ω ∂Q.measure, ∀ n : ℕ, ∀ x : Vec d,
          ENNReal.ofReal (δ n) • ProbabilityTheory.cond (volume : Measure (Vec d))
            (endpointBall (Renewal.forceCoord hd) (L n / lam) x) ≤
          (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L n / lam)
            (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
        ∀ n, ∃ K : CoupledQuenchedLaws d,
          IsRegenerationCoupling hd Q lam (L n) (δ n) h0.le h1 P K)
    (hGuard : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt)
      {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : CoupledSample d → ℝ),
        @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
        let Δ := Renewal.regenDelta lam
        let μ := annealedCoupledLaw Q.measure K
        let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
          {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}))
    (hLocal : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
        (K p).map (recenterSample p.1) = K (0, translate p.1 p.2)) ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
        (∀ᵐ y ∂(volume : Measure (Vec d)), η ≤ ∫ ω,
          ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
            ((y, ω), z) ∂K (y, ω) ∂Q.measure) ∧
        ∀ m J N k : ℕ, ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x (Renewal.forceCoord hd) ≤
            y (Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
          (fun ω => ∫ z, (couplingScopeTrialBurnPrebridge (Renewal.regenDelta lam)
            lam (l / lam) m (Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ)) z *
            (if y ∈ endpointBall (Renewal.forceCoord hd) (l / lam)
              (z.1 (((m + k : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) then 1 else 0)
            ∂K (0, ω)) =ᵐ[Q.measure] A)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  apply c19_s3_clean_scope_assembly ?_ htails
  intro ht d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD k
  obtain ⟨ε, hε, hε1, hguard⟩ := hGuard ht hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  obtain ⟨hcov, η, hη, hη1, hmean, hpast⟩ := hLocal hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  have hlower : ∀ m J N k : ℕ,
      let Δ := Renewal.regenDelta lam
      let R := l / lam
      let i := Renewal.forceCoord hd
      let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
      η * (∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂K (0, ω) ∂Q.measure) ≤
        ∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z *
          endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
            (fun y => ∫ w, killedFutureTest R i (fun _ => 1)
              ((y, ω), w) ∂K (y, ω)) ∂K (0, ω) ∂Q.measure := by
    intro m J N k
    exact c7_clean_burn_endpoint_of_local_past hFuture hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hcov m k
      (couplingScopeTrialBurnPrebridge (Renewal.regenDelta lam) lam (l / lam) m (Renewal.forceCoord hd) J N k)
      (c1_s3_measurableSet_trial_burn_prebridge _ _ _ _ _ _ _ _) η hmean (hpast m J N k)
  have hall := c7_s3_all_cycles_of_countable_cofinal_and_endpoint ht hd Q lam h0 h1 P
    (hCofinal hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD) l δ hl hδ0 hδ1 K hK ε hε hε1 hguard η hη hη1 hlower
  filter_upwards [hall] with q hq
  exact hq k

/-- Clean scope from cofinal couplings, a guard estimate, and literal Burn-past locality. -/
theorem c7_s3_clean_scope_of_cofinal_guard_burn_past
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hCofinal : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
      (L₀ : ℝ), ∃ L δ : ℕ → ℝ,
        (∀ n : ℕ, L₀ + (n : ℝ) ≤ L n ∧ 0 < L n ∧ 0 < δ n ∧ δ n < 1) ∧
        (∀ᵐ ω ∂Q.measure, ∀ n : ℕ, ∀ x : Vec d,
          ENNReal.ofReal (δ n) • ProbabilityTheory.cond (volume : Measure (Vec d))
            (endpointBall (Renewal.forceCoord hd) (L n / lam) x) ≤
          (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L n / lam)
            (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
        ∀ n, ∃ K : CoupledQuenchedLaws d,
          IsRegenerationCoupling hd Q lam (L n) (δ n) h0.le h1 P K)
    (hGuard : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt)
      {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : CoupledSample d → ℝ),
        @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
        let Δ := Renewal.regenDelta lam
        let μ := annealedCoupledLaw Q.measure K
        let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
          {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}))
    (hLocal : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ m J N k : ℕ, ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x (Renewal.forceCoord hd) ≤
            y (Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
          (fun ω => ∫ z, (couplingScopeTrialBurnPrebridge (Renewal.regenDelta lam)
            lam (l / lam) m (Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ)) z *
            (if y ∈ endpointBall (Renewal.forceCoord hd) (l / lam)
              (z.1 (((m + k : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) then 1 else 0)
            ∂K (0, ω)) =ᵐ[Q.measure] A)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  apply c7_s3_clean_scope_of_cofinal_guard_local_past hFuture hCofinal hGuard ?_ htails
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  letI := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  refine ⟨c19_clean_actual_coupled_covariance hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK,
    (annealedCoupledLaw Q.measure K).real (regenerationNoReturn hd (l / lam)),
    ENNReal.toReal_pos hD (measure_ne_top _ _), measureReal_le_one, ?_,
    hLocal hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD⟩
  filter_upwards [c19_clean_actual_killed_future_one_mean hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK] with y hy
  exact le_of_eq hy.symm

/-- The stopped-tube estimate supplies the literal even-guard estimate. -/
theorem c7_s3_clean_scope_of_cofinal_tube_burn_past
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hCofinal : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
      (L₀ : ℝ), ∃ L δ : ℕ → ℝ,
        (∀ n : ℕ, L₀ + (n : ℝ) ≤ L n ∧ 0 < L n ∧ 0 < δ n ∧ δ n < 1) ∧
        (∀ᵐ ω ∂Q.measure, ∀ n : ℕ, ∀ x : Vec d,
          ENNReal.ofReal (δ n) • ProbabilityTheory.cond (volume : Measure (Vec d))
            (endpointBall (Renewal.forceCoord hd) (L n / lam) x) ≤
          (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L n / lam)
            (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) ∧
        ∀ n, ∃ K : CoupledQuenchedLaws d,
          IsRegenerationCoupling hd Q lam (L n) (δ n) h0.le h1 P K)
    (hTube : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube))
    (hLocal : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ m J N k : ℕ, ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x (Renewal.forceCoord hd) ≤
            y (Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
          (fun ω => ∫ z, (couplingScopeTrialBurnPrebridge (Renewal.regenDelta lam)
            lam (l / lam) m (Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ)) z *
            (if y ∈ endpointBall (Renewal.forceCoord hd) (l / lam)
              (z.1 (((m + k : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) then 1 else 0)
            ∂K (0, ω)) =ᵐ[Q.measure] A)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  apply c7_s3_clean_scope_of_cofinal_guard_burn_past hFuture hCofinal ?_ hLocal htails
  intro ht d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  exact c10_clean_s3_actual_guard_of_stopped_tube hTube ht hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD

/-- Cofinal endpoint density and the stopped-tube estimate supply the scope inputs. -/
theorem c7_s3_clean_scope_of_cofinal_density_tube_burn_past
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hDensity : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧
        ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
          ∀ A : Set (Vec d), MeasurableSet A →
            ENNReal.ofReal c * volume (endpointBall (Renewal.forceCoord hd) (L / lam) x ∩ A) ≤
            P (x, ω) {γ | (∀ t : ℝ≥0, t ≤ Renewal.regenDelta lam →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (L / lam) x) ∧
              γ (Renewal.regenDelta lam) ∈ A})
    (hTube : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube))
    (hLocal : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ m J N k : ℕ, ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x (Renewal.forceCoord hd) ≤
            y (Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
          (fun ω => ∫ z, (couplingScopeTrialBurnPrebridge (Renewal.regenDelta lam)
            lam (l / lam) m (Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ)) z *
            (if y ∈ endpointBall (Renewal.forceCoord hd) (l / lam)
              (z.1 (((m + k : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) then 1 else 0)
            ∂K (0, ω)) =ᵐ[Q.measure] A)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  apply c7_s3_clean_scope_of_cofinal_tube_burn_past hFuture ?_ hTube hLocal htails
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD L₀
  exact c4_cofinal_family_of_endpoint_density hd Q lam h0 h1 P hK.2.2.1
    (hDensity hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD) L₀

/-- The actual past kernel supplies Burn-prefix locality. -/
theorem c7_s3_clean_scope_of_cofinal_density_tube
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hDensity : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧
        ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
          ∀ A : Set (Vec d), MeasurableSet A →
            ENNReal.ofReal c * volume (endpointBall (Renewal.forceCoord hd) (L / lam) x ∩ A) ≤
            P (x, ω) {γ | (∀ t : ℝ≥0, t ≤ Renewal.regenDelta lam →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (L / lam) x) ∧
              γ (Renewal.regenDelta lam) ∈ A})
    (hTube : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube))
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  apply c7_s3_clean_scope_of_cofinal_density_tube_burn_past hFuture hDensity hTube ?_ htails
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  obtain ⟨_, η, _, _, _, hlocal⟩ :=
    c1_s3_clean_burn_past_of_literal_past_kernel EinsteinFull.c10_actual_past_kernel
      hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  exact hlocal

/-- Selected fixed-time density supplies the stopped-tube input. -/
theorem c7_s3_clean_scope_of_cofinal_density_selected_lower
    (hFuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt)
    (hDensity : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
      (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ B : ℝ, ∃ L : ℝ, B ≤ L ∧ 0 < L ∧
        ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
          ∀ A : Set (Vec d), MeasurableSet A →
            ENNReal.ofReal c * volume (endpointBall (Renewal.forceCoord hd) (L / lam) x ∩ A) ≤
            P (x, ω) {γ | (∀ t : ℝ≥0, t ≤ Renewal.regenDelta lam →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (L / lam) x) ∧
              γ (Renewal.regenDelta lam) ∈ A})
    (hSelected : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l : ℝ), 0 < l → ∀ (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P →
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure,
        ∃ (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
          (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
            (one_le_sourceReducedBound Q.ellipticity_parameter)
            (zeroPotentialReducedPair ω) hω lam h0.le h1),
        (∀ x : Vec d, P (x, ω) = G.pathLaw x) ∧
        ∀ (x : Vec d) (A : Set (Vec d)), MeasurableSet A →
          A ⊆ {y | euclideanNorm (y - x) < ((l / lam) / 2) / 16} →
          ENNReal.ofReal c * volume A ≤
            gmpKilledEndpointKernel G (PDE.euclideanBall x ((l / lam) / 2))
              (PDE.isOpen_euclideanBall x ((l / lam) / 2))
              (Regeneration.Renewal.regenDelta lam) x A)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  apply c7_s3_clean_scope_of_cofinal_density_tube hFuture hDensity ?_ htails
  intro ht d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  exact c4_stopped_tube_of_selected_killed_lower hSelected hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK

end EinsteinFull.Blueprint
