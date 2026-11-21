import EinsteinFull.Regeneration.AnnealedHistoryRestart
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3HistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.AnnealedHistoryRestart`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of `EinsteinFull.Regeneration.lintegral_history_restart`. -/
theorem lintegral_history_restart_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) (m : ℕ)
    (G : CoupledSample d × CoupledSample d → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ q, G (EinsteinRelation.Probability.stoppedHistorySample (Renewal.regenDelta lam) m q.2,
        sampleTimeShift (Renewal.regenDelta lam) q.2 ((m : ℝ≥0) * Renewal.regenDelta lam))
        ∂annealedCoupledLaw Q.measure K) =
      ∫⁻ q, ∫⁻ w, G (EinsteinRelation.Probability.stoppedHistorySample
          (Renewal.regenDelta lam) m q.2, w)
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ∂annealedCoupledLaw Q.measure K := by
  let Δ := Renewal.regenDelta lam
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure Q.measure := Q.probability
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let X : FieldPair d × CoupledSample d → CoupledSample d :=
    fun q => EinsteinRelation.Probability.stoppedHistorySample Δ m q.2
  have hX : Measurable X :=
    ((EinsteinRelation.Probability.measurable_stoppedHistorySample Δ m).mono
      (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl).comp measurable_snd
  let Y : FieldPair d × CoupledSample d → CoupledSample d :=
    fun q => sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
  have hY : Measurable Y := (measurable_sampleTimeShift Δ).comp
    (measurable_const.prodMk measurable_snd)
  let E : FieldPair d × CoupledSample d → Vec d × FieldPair d :=
    fun q => (q.2.1 ((m : ℝ≥0) * Δ), q.1)
  have hE : Measurable E := ((continuous_eval_const _).measurable.comp
    measurable_snd.fst).prodMk measurable_fst
  let L : Kernel (FieldPair d × CoupledSample d) (CoupledSample d) :=
    (EinsteinRelation.Probability.probabilityPart K).comap E hE
  have hp := EinsteinFull.Blueprint.c10_s3_grid_endpoint_probability_phys hd Q lam h0 h1 l δ P K hK m
  have hLK : ∀ᵐ q ∂μ, L q = K (E q) := by
    filter_upwards [hp] with q hq
    have := hq
    simp only [L, Kernel.comap_apply,
      EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
  have hpair : μ.map (fun q => (X q, Y q)) = (μ.compProd L).map (fun q => (X q.1, q.2)) := by
    apply map_pair_eq_restart_of_product_tests μ X Y hX hY L
    intro H Φ hH hbH hΦ hbΦ
    have hr := EinsteinFull.Blueprint.c10_s3_history_parameter_restart_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK m
      (fun p => H p.1 * Φ p.2) ((hH.comp measurable_fst).mul (hΦ.comp measurable_snd))
      (by
        obtain ⟨A, hA⟩ := hbH
        obtain ⟨B, hB⟩ := hbΦ
        refine ⟨A * B, fun p => ?_⟩
        rw [abs_mul]
        exact mul_le_mul (hA _) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hA p.1)))
    simp only at hr
    refine hr.trans (integral_congr_ae ?_)
    filter_upwards [hLK] with q hq
    simp only [X, hq, integral_const_mul]
    rfl
  calc (∫⁻ q, G (X q, Y q) ∂μ)
      = ∫⁻ p, G p ∂(μ.map (fun q => (X q, Y q))) :=
        (lintegral_map hG (hX.prodMk hY)).symm
    _ = ∫⁻ p, G p ∂((μ.compProd L).map (fun q => (X q.1, q.2))) := by rw [hpair]
    _ = ∫⁻ q, G (X q.1, q.2) ∂(μ.compProd L) :=
        lintegral_map hG ((hX.comp measurable_fst).prodMk measurable_snd)
    _ = ∫⁻ q, ∫⁻ w, G (X q, w) ∂L q ∂μ :=
        Measure.lintegral_compProd (hG.comp ((hX.comp measurable_fst).prodMk measurable_snd))
    _ = ∫⁻ q, ∫⁻ w, G (X q, w) ∂K (E q) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hLK] with q hq
        rw [hq]

/-- The physical-kernel version of `EinsteinFull.Regeneration.lintegral_grid_stopping_le`. -/
theorem lintegral_grid_stopping_le_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (T : CoupledSample d → ℝ≥0∞) (hT : Measurable T)
    (hgrid : ∀ z, T z ≠ ⊤ → ∃ m : ℕ,
      T z = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞))
    (W : CoupledSample d → ℝ≥0∞) (hW : Measurable W)
    (Φ : CoupledSample d × CoupledSample d → ℝ≥0∞) (hΦ : Measurable Φ)
    (hpre : ∀ (m : ℕ) (z : CoupledSample d),
      (T z = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ↔
        T (EinsteinRelation.Probability.stoppedHistorySample (Renewal.regenDelta lam) m z) =
          (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)) ∧
      (T z = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) →
        W (EinsteinRelation.Probability.stoppedHistorySample (Renewal.regenDelta lam) m z) = W z ∧
        ∀ w, Φ (EinsteinRelation.Probability.stoppedHistorySample (Renewal.regenDelta lam) m z, w) =
          Φ (z, w)))
    (B : ℝ≥0∞)
    (hinner : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      T q.2 = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) →
      ∫⁻ w, Φ (q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ B) :
    (∫⁻ q, {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator
        (fun q => W q.2 * Φ (q.2, sampleTimeShift (Renewal.regenDelta lam) q.2 (T q.2).toNNReal)) q
        ∂annealedCoupledLaw Q.measure K) ≤
      B * ∫⁻ q, {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator (fun q => W q.2) q
        ∂annealedCoupledLaw Q.measure K := by
  let Δ := Renewal.regenDelta lam
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  let μ := annealedCoupledLaw Q.measure K
  let g : ℕ → ℝ≥0∞ := fun m => (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)
  let S : ℕ → CoupledSample d → CoupledSample d := fun m =>
    EinsteinRelation.Probability.stoppedHistorySample Δ m
  have hS : ∀ m, Measurable (S m) := fun m =>
    (EinsteinRelation.Probability.measurable_stoppedHistorySample Δ m).mono
      (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl
  let G : ℕ → CoupledSample d × CoupledSample d → ℝ≥0∞ := fun m p =>
    if T p.1 = g m then W p.1 * Φ p else 0
  have hG : ∀ m, Measurable (G m) := fun m =>
    Measurable.ite (measurableSet_eq_fun (hT.comp measurable_fst) measurable_const)
      ((hW.comp measurable_fst).mul hΦ) measurable_const
  have hslice : ∀ (m : ℕ) (z w : CoupledSample d),
      G m (S m z, w) = if T z = g m then W z * Φ (z, w) else 0 := by
    intro m z w
    have h := hpre m z
    show (if T (S m z) = g m then W (S m z) * Φ (S m z, w) else 0) = _
    by_cases hz : T z = g m
    · rw [ite_eq_left (h.1.mp hz), ite_eq_left hz, (h.2 hz).1, (h.2 hz).2 w]
    · have hz' : ¬ T (S m z) = g m := fun h' => hz (h.1.mpr h')
      rw [ite_eq_right hz, ite_eq_right hz']
  have hsplit : ∀ (F : ℕ → CoupledSample d → ℝ≥0∞) (F₀ : CoupledSample d → ℝ≥0∞)
      (z : CoupledSample d), (∀ m, T z = g m → F m z = F₀ z) →
      {z : CoupledSample d | T z ≠ ⊤}.indicator F₀ z =
        ∑' m : ℕ, if T z = g m then F m z else 0 := by
    intro F F₀ z hF
    by_cases htop : T z = ⊤
    · have hne : ∀ m, ¬ T z = g m := by
        intro m hm
        rw [hm] at htop
        exact ENNReal.coe_ne_top htop
      simp only [hne, ite_false, tsum_zero]
      exact Set.indicator_of_notMem (show z ∉ {z : CoupledSample d | T z ≠ ⊤} from
        fun h => h htop) _
    · obtain ⟨m, hm⟩ := hgrid z htop
      rw [tsum_eq_single m, ite_eq_left hm, Set.indicator_of_mem htop, hF m hm]
      intro n hn
      rw [ite_eq_right]
      intro hn'
      exact hn (grid_index_unique Δ hΔ (hn'.symm.trans hm))
  have hL : ∀ q : FieldPair d × CoupledSample d,
      {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator
        (fun q => W q.2 * Φ (q.2, sampleTimeShift Δ q.2 (T q.2).toNNReal)) q =
      ∑' m : ℕ, G m (S m q.2, sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) := by
    intro q
    simp only [hslice]
    have h := hsplit (fun m z => W z * Φ (z, sampleTimeShift Δ z ((m : ℝ≥0) * Δ)))
      (fun z => W z * Φ (z, sampleTimeShift Δ z (T z).toNNReal)) q.2
      (fun m hm => by rw [hm, ENNReal.toNNReal_coe])
    have hind : {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator
        (fun q => W q.2 * Φ (q.2, sampleTimeShift Δ q.2 (T q.2).toNNReal)) q =
        {z : CoupledSample d | T z ≠ ⊤}.indicator
          (fun z => W z * Φ (z, sampleTimeShift Δ z (T z).toNNReal)) q.2 := by
      rfl
    rw [hind, h]
  have hmeasL : ∀ m, Measurable (fun q : FieldPair d × CoupledSample d =>
      G m (S m q.2, sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ))) := fun m =>
    (hG m).comp (((hS m).comp measurable_snd).prodMk
      ((measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)))
  have hR : ∀ q : FieldPair d × CoupledSample d,
      {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator (fun q => B * W q.2) q =
      ∑' m : ℕ, if T q.2 = g m then B * W q.2 else 0 := by
    intro q
    have h := hsplit (fun _ z => B * W z) (fun z => B * W z) q.2 (fun _ _ => rfl)
    have hind : {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator
        (fun q => B * W q.2) q =
        {z : CoupledSample d | T z ≠ ⊤}.indicator (fun z => B * W z) q.2 := by
      rfl
    rw [hind, h]
  have hTset : MeasurableSet {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤} :=
    (measurableSet_eq_fun (hT.comp measurable_snd) measurable_const).compl
  calc (∫⁻ q, {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator
          (fun q => W q.2 * Φ (q.2, sampleTimeShift Δ q.2 (T q.2).toNNReal)) q ∂μ)
      = ∫⁻ q, ∑' m : ℕ, G m (S m q.2, sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ := by
        simp only [hL]
    _ = ∑' m : ℕ, ∫⁻ q, G m (S m q.2, sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ :=
        lintegral_tsum fun m => (hmeasL m).aemeasurable
    _ = ∑' m : ℕ, ∫⁻ q, ∫⁻ w, G m (S m q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1) ∂μ := by
        congr 1
        funext m
        exact lintegral_history_restart_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK m (G m) (hG m)
    _ ≤ ∑' m : ℕ, ∫⁻ q, (if T q.2 = g m then B * W q.2 else 0) ∂μ := by
        refine ENNReal.tsum_le_tsum fun m => lintegral_mono_ae ?_
        filter_upwards [hinner] with q hq
        simp only [hslice]
        by_cases hm : T q.2 = g m
        · simp only [ite_eq_left hm]
          have hΦq : Measurable (fun w : CoupledSample d => Φ (q.2, w)) :=
            hΦ.comp (measurable_const.prodMk measurable_id)
          rw [lintegral_const_mul (W q.2) hΦq, mul_comm]
          gcongr
          exact hq m hm
        · simp only [ite_eq_right hm, lintegral_zero, le_refl]
    _ = ∫⁻ q, ∑' m : ℕ, (if T q.2 = g m then B * W q.2 else 0) ∂μ := by
        rw [lintegral_tsum]
        intro m
        exact (Measurable.ite (measurableSet_eq_fun (hT.comp measurable_snd) measurable_const)
          (measurable_const.mul (hW.comp measurable_snd)) measurable_const).aemeasurable
    _ = ∫⁻ q, {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator
          (fun q => B * W q.2) q ∂μ := by
        simp only [hR]
    _ = B * ∫⁻ q, {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator
          (fun q => W q.2) q ∂μ := by
        have hmeasW : Measurable (fun q : FieldPair d × CoupledSample d =>
            {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator (fun q => W q.2) q) :=
          (hW.comp measurable_snd).indicator hTset
        rw [← lintegral_const_mul B hmeasW]
        congr 1
        funext q
        simp only [Set.indicator, Set.mem_ofPred_eq]
        split_ifs <;> simp

/-- The physical-kernel version of
`EinsteinFull.Regeneration.lintegral_grid_stopping_le_of_decided`. -/
theorem lintegral_grid_stopping_le_of_decided_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (T : CoupledSample d → ℝ≥0∞) (hT : Measurable T)
    (hgrid : ∀ z, T z ≠ ⊤ → ∃ m : ℕ,
      T z = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞))
    (W : CoupledSample d → ℝ≥0∞) (hW : Measurable W)
    (Φ : CoupledSample d × CoupledSample d → ℝ≥0∞) (hΦ : Measurable Φ)
    (hdec : HistoryDecided (Renewal.regenDelta lam) T
      (fun z => (W z, fun w => Φ (z, w))))
    (B : ℝ≥0∞)
    (hinner : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      T q.2 = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) →
      ∫⁻ w, Φ (q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ B) :
    (∫⁻ q, {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator
        (fun q => W q.2 * Φ (q.2, sampleTimeShift (Renewal.regenDelta lam) q.2 (T q.2).toNNReal)) q
        ∂annealedCoupledLaw Q.measure K) ≤
      B * ∫⁻ q, {q : FieldPair d × CoupledSample d | T q.2 ≠ ⊤}.indicator (fun q => W q.2) q
        ∂annealedCoupledLaw Q.measure K := by
  apply lintegral_grid_stopping_le_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK T hT hgrid W hW Φ hΦ
    _ B hinner
  intro m z
  have hag := historyAgree_stoppedHistorySample (Renewal.regenDelta lam) m z
  refine ⟨⟨fun hz => (hdec m z _ hag hz).1.trans hz, fun hz => ?_⟩, fun hz => ?_⟩
  · exact (hdec m _ z hag.symm hz).1.trans hz
  · obtain ⟨_, hF⟩ := hdec m z _ hag hz
    simp only [Prod.mk.injEq] at hF
    exact ⟨hF.1, fun w => congrFun hF.2 w⟩

end EinsteinFull.Regeneration
