import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinRelation.Regeneration.AnnealedUniformEndpointRestart
import EinsteinRelation.Regeneration.FirstRegenerationFiniteness
import EinsteinRelation.Regeneration.RenewalRecordIteration

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- A measurable path event transfers between couplings with the same path marginal. -/
theorem c19_s3_transfer_path_event {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (K K' : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hK' : HasProbabilityLaws Q K')
    (hM : HasPathMarginals Q K P) (hM' : HasPathMarginals Q K' P)
    (A : Set (Path d)) (hA : MeasurableSet A)
    (h : ∀ᵐ q ∂annealedCoupledLaw Q K, q.2.1 ∈ A) :
    ∀ᵐ q ∂annealedCoupledLaw Q K', q.2.1 ∈ A := by
  have hf := ae_quenched_of_annealed Q K hK h
  have hp : ∀ᵐ ω ∂Q, ∀ᵐ x ∂P (0, ω), x ∈ A := by
    filter_upwards [hf, hM.1] with ω hfω hmap
    rw [← hmap]
    exact (ae_map_iff measurable_fst.aemeasurable hA).2 hfω
  apply Measure.ae_compProd_of_ae_ae (hA.preimage measurable_snd.fst)
  filter_upwards [hp, hK'.1, hM'.1] with ω hpω hprob hmap
  let : IsProbabilityMeasure (originCoupledLaw K' ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K') ω]
  apply ae_of_ae_map measurable_fst.aemeasurable
  change ∀ᵐ y ∂(K' (0, ω)).map Prod.fst, y ∈ A
  rwa [hmap]

/-- A path eventually stays above a fixed displacement. -/
@[nolint defsWithUnderscore]
def c19_s3_eventual_displacement {d : ℕ} (i : Fin d) (R : ℝ) : Set (Path d) :=
  {γ | ∃ n : ℕ, ∀ t : ℝ≥0, (n : ℝ≥0) ≤ t → R ≤ γ t i - γ 0 i}

/-- Eventual displacement is measurable, by closedness at each fixed time. -/
theorem c19_s3_measurableSet_eventual_displacement {d : ℕ} (i : Fin d) (R : ℝ) :
    MeasurableSet (c19_s3_eventual_displacement i R) := by
  have heq : c19_s3_eventual_displacement i R =
      ⋃ n : ℕ, ⋂ t : ℝ≥0, ⋂ (_ : (n : ℝ≥0) ≤ t),
        {γ : Path d | R ≤ γ t i - γ 0 i} := by
    ext γ
    simp only [c19_s3_eventual_displacement, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_iInter]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro ht
  apply isClosed_le continuous_const
  have heval (s : ℝ≥0) : Continuous (fun γ : Path d => γ s i) :=
    (continuous_apply i).comp (continuous_eval_const s)
  exact (heval t).sub (heval 0)

/-- Any eventual displacement bound admits a natural start time. -/
theorem c19_s3_mem_eventual_displacement {d : ℕ} (i : Fin d) (R : ℝ)
    (γ : Path d) (T : ℝ≥0)
    (h : ∀ t : ℝ≥0, T ≤ t → R ≤ γ t i - γ 0 i) :
    γ ∈ c19_s3_eventual_displacement i R := by
  obtain ⟨n, hn⟩ := exists_nat_ge T
  exact ⟨n, fun t ht => h t (hn.trans ht)⟩

/-- Cofinal eventual displacement bounds force escape to positive infinity. -/
theorem c19_s3_escape_of_eventual_displacement {d : ℕ} (i : Fin d) (γ : Path d)
    (h : ∀ n : ℕ, γ ∈ c19_s3_eventual_displacement i n) :
    Filter.Tendsto (fun t : ℝ≥0 => γ t i) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt (B - γ 0 i)
  obtain ⟨m, hm⟩ := h n
  filter_upwards [Filter.eventually_ge_atTop (m : ℝ≥0)] with t ht
  have hbound := hm t ht
  linarith

/-- A finite first regeneration and the bridge floor give an eventual bound. -/
theorem c19_s3_eventual_displacement_of_first_floor {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (hsupport : HasSuccessfulBridgeSupport Q Δ i R K)
    (hfin : ∀ᵐ q ∂annealedCoupledLaw Q K,
      firstRegenerationTime Δ lam R q.2 i ≠ ⊤)
    (hfloor : ∀ z : CoupledSample d,
      firstRegenerationTime Δ lam R z i ≠ ⊤ →
      (∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
        (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
          z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ))) →
      ∀ t : ℝ≥0, (firstRegenerationTime Δ lam R z i).toNNReal ≤ t →
        R < z.1 t i - z.1 0 i) :
    ∀ᵐ q ∂annealedCoupledLaw Q K, q.2.1 ∈ c19_s3_eventual_displacement i R := by
  have hfinite := ae_quenched_of_annealed Q K hK hfin
  apply Measure.ae_compProd_of_ae_ae
    ((c19_s3_measurableSet_eventual_displacement i R).preimage measurable_snd.fst)
  filter_upwards [hK.1, hsupport.1, hfinite] with ω hprob hbridge hτ
  let : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  filter_upwards [hbridge, hτ] with z hz hzt
  apply c19_s3_mem_eventual_displacement i R z.1
    (firstRegenerationTime Δ lam R z i).toNNReal
  intro t ht
  exact le_of_lt (hfloor z hzt hz t ht)

@[nolint unusedArguments]
theorem c19_s3_escape_of_tails_cofinal_couplings
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (c1_s3_first_regeneration_future_floor : ∀ {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
      (hlam : 0 < lam) (hR : 0 < R) (z : CoupledSample d) (i : Fin d),
      firstRegenerationTime Δ lam R z i ≠ ⊤ →
      (∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
        (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
          z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ))) →
      ∀ t : ℝ≥0, (firstRegenerationTime Δ lam R z i).toNNReal ≤ t →
        R < z.1 t i - z.1 0 i)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hSplits : ∀ L : ℝ, 0 < L → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ K : CoupledQuenchedLaws d, IsRegenerationCoupling hd Q lam L δ h0.le h1 P K)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t (Renewal.forceCoord hd)) Filter.atTop Filter.atTop := by
  obtain ⟨L₀, hL₀, _, htail⟩ := htails d hd Λ₀ r₀
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  have hall : ∀ n : ℕ, ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      q.2.1 ∈ c19_s3_eventual_displacement (Renewal.forceCoord hd) n := by
    intro n
    let L : ℝ := L₀ + (n : ℝ) * lam
    have hL : 0 < L := by dsimp [L]; positivity
    have hLge : L₀ ≤ L := by dsimp [L]; nlinarith
    have hn : (n : ℝ) ≤ L / lam := by
      apply (le_div_iff₀ h0).2
      dsimp [L]
      linarith
    obtain ⟨δ', hδ'0, hδ'1, K', hK'⟩ := hSplits L hL
    obtain ⟨c, C, a, M, hc, _, _, _, _, htail'⟩ := htail L hLge δ' hδ'0 hδ'1
    obtain ⟨_, _, htail'', _, _⟩ := htail' Q lam h0 h1 P K' hK'
    have ht : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam)
        lam (L / lam) c C (Renewal.forceCoord hd) K' := by
      intro t ht
      simpa only [EinsteinFull.regenerationTime, Regeneration.regenerationTime_one] using htail'' t ht
    have hfin := firstRegenerationTime_ne_top_ae_of_tail Q.measure K'
      (Renewal.regenDelta lam) lam (L / lam) c C hc h0 (Renewal.forceCoord hd) ht
    have hev := c19_s3_eventual_displacement_of_first_floor Q.measure K' hK'.1
      (Renewal.regenDelta lam) lam (L / lam) (Renewal.forceCoord hd)
      hK'.2.2.2.2.2.1 hfin
      (fun z => c1_s3_first_regeneration_future_floor _ hΔ lam (L / lam) h0
        (div_pos hL h0) z (Renewal.forceCoord hd))
    have htransfer := c19_s3_transfer_path_event Q.measure P K' K hK'.1 hK.1
      hK'.2.1 hK.2.1 _ (c19_s3_measurableSet_eventual_displacement _ _) hev
    filter_upwards [htransfer] with q hq
    obtain ⟨m, hm⟩ := hq
    exact ⟨m, fun t ht => hn.trans (hm t ht)⟩
  filter_upwards [ae_all_iff.mpr hall] with q hq
  exact c19_s3_escape_of_eventual_displacement (Renewal.forceCoord hd) q.2.1 hq

end EinsteinFull.Blueprint
