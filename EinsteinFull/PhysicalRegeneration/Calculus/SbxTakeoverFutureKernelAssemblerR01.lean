import EinsteinFull.Calculus.SbxTakeoverFutureKernelAssemblerR01
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS2FutureKernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS8FutureKernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Calculus.C9FutureKernelIndicatorLocality
import EinsteinFull.PhysicalRegeneration.Calculus.SunaS2RationalStoppedLaw
import EinsteinFull.PhysicalRegeneration.Calculus.SunaS2SuppliedStoppedLocality
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledHistoryHalfSpaceLocality
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxTakeoverFutureKernelAssemblerR01`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxTakeoverR01_killedPathBit_versions_of_resampling_finiteStoppedKilledHistory`. -/
theorem sbxTakeoverR01_killedPathBit_versions_of_resampling_finiteStoppedKilledHistory_phys
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀ h₁ P K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (hR : 0 < R) (i : Fin d)
    (hfinite : ∀ n : ℕ, ∀ᵐ ω ∂Q.measure,
      ∀ᵐ ω' ∂condExpKernel Q.measure (localSigma {x : Vec d | -2 * R ≤ x i}) ω,
        sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
          sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i n) :
    HasKilledPathBitFutureVersions Q.measure i R K := by
  let m := localSigma {x : Vec d | -2 * R ≤ x i}
  let : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hm := Probability.localSigma_le_borel {x : Vec d | -2 * R ≤ x i}
  have hstop := sbxS8_killedPathBitKernel_stopped_of_coupling_phys
    hd Q lam l δ h₀ h₁ P K hK R hR i
  have hcopies : ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂condExpKernel Q.measure m ω,
      sbxS8KilledPathBitKernel R i K ω' =
        (sbxS2StoppedOriginKernel R i K ω').restrict
          {z | NoBacktracking R z.1 i} := by
    have hc : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
        sbxS8KilledPathBitKernel R i K ω' =
          (sbxS2StoppedOriginKernel R i K ω').restrict
            {z | NoBacktracking R z.1 i} := by
      rw [condExpKernel_comp_trim hm]
      exact hstop
    exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hc)
  have hall : ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂condExpKernel Q.measure m ω, ∀ n : ℕ,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
        sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i n := by
    filter_upwards [ae_all_iff.mpr hfinite] with ω hω
    exact ae_all_iff.mpr hω
  apply sbxTakeoverR01_killedPathBit_versions_of_resampling_kernel_eq Q.measure K hK.1 R i
  filter_upwards [hstop, hcopies, hall] with ω hs hc hn
  filter_upwards [hc, hn] with ω' hs' hnn
  have : IsFiniteMeasure (sbxS2StoppedOriginKernel R i K ω) := by
    unfold sbxS2StoppedOriginKernel
    infer_instance
  have : IsFiniteMeasure (sbxS2StoppedOriginKernel R i K ω') := by
    unfold sbxS2StoppedOriginKernel
    infer_instance
  rw [hs, hs']
  exact sbxS8_killedMeasure_eq_of_finiteKilledHistory
    (sbxS2StoppedOriginKernel R i K ω) (sbxS2StoppedOriginKernel R i K ω')
    Δ hΔ R i hnn

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxTakeoverMinimalR01_future_kernel_of_finite_histories`. -/
theorem sbxTakeoverMinimalR01_future_kernel_of_finite_histories_phys
    (hfinite :
      ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
        (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
        (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ0 : 0 < δ) (_hδ1 : δ < 1)
        (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
        (_hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K),
        ∀ n : ℕ, ∀ᵐ ω ∂Q.measure,
          ∀ᵐ ω' ∂condExpKernel Q.measure
            (localSigma {x : Vec d | -2 * (l / lam) ≤ x (Renewal.forceCoord hd)}) ω,
            sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel (l / lam)
              (Renewal.forceCoord hd) K ω) (Renewal.regenDelta lam) (l / lam)
              (Renewal.forceCoord hd) n =
            sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel (l / lam)
              (Renewal.forceCoord hd) K ω') (Renewal.regenDelta lam) (l / lam)
              (Renewal.forceCoord hd) n) :
    node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK Φ hΦ _hb
  apply sbxTakeoverMinimalR01_joint_future_versions Q.measure K hK.1 (l / lam)
    (Renewal.forceCoord hd)
  · apply future_product_versions_of_killed_path_bit Q.measure (Renewal.forceCoord hd)
      (l / lam) K
    exact sbxTakeoverR01_killedPathBit_versions_of_resampling_finiteStoppedKilledHistory_phys
      hd Q lam l δ h0.le h1 P K hK (Renewal.regenDelta lam)
      (EinsteinRelation.regenDelta_pos h0) (l / lam) (div_pos hl h0)
      (Renewal.forceCoord hd)
      (hfinite hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK)
  · exact hΦ

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxTakeoverMinimalR01_s3_finite_killed_history_zero`. -/
theorem sbxTakeoverMinimalR01_s3_finite_killed_history_zero_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂ProbabilityTheory.condExpKernel Q.measure
      (localSigma {x : Vec d | -2 * (l / lam) ≤ x (Regeneration.Renewal.forceCoord hd)}) ω,
      sbxS8FiniteKilledHistory
        (sbxS2StoppedOriginKernel (l / lam) (Regeneration.Renewal.forceCoord hd) K ω)
        (Regeneration.Renewal.regenDelta lam) (l / lam) (Regeneration.Renewal.forceCoord hd) 0 =
      sbxS8FiniteKilledHistory
        (sbxS2StoppedOriginKernel (l / lam) (Regeneration.Renewal.forceCoord hd) K ω')
        (Regeneration.Renewal.regenDelta lam) (l / lam) (Regeneration.Renewal.forceCoord hd) 0 := by
  classical
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let Δ := Regeneration.Renewal.regenDelta lam
  let m := localSigma {x : Vec d | -2 * R ≤ x i}
  let : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hR : 0 < R := div_pos hl h0
  have hb : sbxS8FutureBarrier Δ R i 0 = Set.univ := by
    ext z
    simp only [sbxS8FutureBarrier, Set.mem_ofPred_eq, Set.mem_univ, iff_true, Nat.cast_zero, zero_mul]
    intro t ht
    have : t = 0 := le_antisymm ht zero_le
    subst t
    simp [hR]
  let z0 : CoupledSample d := (ContinuousMap.const ℝ≥0 0, fun _ => false)
  have hf : ∀ᵐ ω ∂Q.measure,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i 0 = Measure.dirac z0 := by
    filter_upwards [hK.1.1, future_locality_ae_starts_at_origin_of_coupling_phys hd Q lam l δ h0.le h1 P K hK] with ω hp hs
    have : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    rw [sbxS8FiniteKilledHistory, hb, Measure.restrict_univ,
      sbxS2StoppedOriginKernel, Kernel.map_apply _ (sbxS2_measurable_stopFutureSample R i),
      Probability.probabilityPart_eq_of_isProbabilityMeasure,
      Measure.map_map (sbxS8_measurable_stoppedHistorySample Δ 0) (sbxS2_measurable_stopFutureSample R i)]
    calc
      _ = Measure.map (fun _ : CoupledSample d => z0) (originCoupledLaw K ω) := by
        apply Measure.map_congr
        filter_upwards [hs] with z hz
        apply Prod.ext
        · apply ContinuousMap.ext
          intro t
          simp [Probability.stoppedHistorySample, sbxS2StopFutureSample,
            localityStoppedPath_zero, hz, z0]
        · funext k
          simp [Probability.stoppedHistorySample, z0]
      _ = Measure.dirac z0 := by simp
  have hm := Probability.localSigma_le_borel {x : Vec d | -2 * R ≤ x i}
  have hc : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i 0 = Measure.dirac z0 := by
    rw [condExpKernel_comp_trim hm]
    exact hf
  have hc' := ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hc)
  filter_upwards [hf, hc'] with ω hω hω'
  filter_upwards [hω'] with ω' hω'
  exact hω.trans hω'.symm

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxTakeoverMinimalR01_future_histories_eq_of_stopped_map_eq`. -/
theorem sbxTakeoverMinimalR01_future_histories_eq_of_stopped_map_eq_phys
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
    (hstop : ∀ y : Vec d, -R ≤ y i →
      (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}))
    (x : Vec d) (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P K (x, ω'))
    (n : ℕ) (hn : 1 ≤ n) (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F)
    (hb : BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R ≤ z.1 t i) :
    (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K (x, ω') := by
  apply integral_supported_histories_eq_of_regular_environments_phys hd Λ₀ hΛ₀ lam h0 h1
    Δ hΔ δ R i P K ω ω' hg hg' {y | -R ≤ y i}
    (isClosed_le continuous_const (continuous_apply i)) ?_ x hx hx' n hn F hF hb hsupport
  intro y hy hyf hyf' G hG hbG hsG
  obtain ⟨hω, r, hr⟩ := hg.1
  obtain ⟨hω', r', hr'⟩ := hg'.1
  have := hyf.1
  have := hyf'.1
  have hs := r.pathLaw_starts_at y
  have hs' := r'.pathLaw_starts_at y
  rw [← hr y, ← hyf.2.1] at hs
  rw [← hr' y, ← hyf'.2.1] at hs'
  exact sbxTakeoverMinimalR01_future_first_history_eq_of_stopped_map_eq Δ δ R hR i P K y ω ω' hy
    (ae_of_ae_map measurable_fst.aemeasurable hs)
    (ae_of_ae_map measurable_fst.aemeasurable hs') hyf.2.2.2 hyf'.2.2.2
    (hstop y hy) G hG hbG (by
      simpa only [Probability.historyStays, Set.mem_ofPred_eq, Nat.cast_one, one_mul] using hsG)

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxTakeoverMinimalR01_future_finite_barrier_eq_of_stopped_map_eq`. -/
theorem sbxTakeoverMinimalR01_future_finite_barrier_eq_of_stopped_map_eq_phys
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
    (hstop : ∀ y : Vec d, -R ≤ y i →
      (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}))
    (m n : ℕ) (hmn : m ≤ n) (hn : 1 ≤ n) (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance F)
    (hb : BoundedRealTest F) :
    (∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
      then F z else 0) ∂K (0, ω)) =
    ∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
      then F z else 0) ∂K (0, ω') := by
  let G : CoupledSample d → ℝ := fun z =>
    if z.1 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
      then F z else 0
  have hzero : @Measurable (CoupledSample d) (Vec d)
      (finiteHistorySigma Δ n) inferInstance (fun z => z.1 0) := by
    have h := ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_fst).comp
      (Probability.measurable_stoppedHistorySample (d := d) Δ n)
    change @Measurable (CoupledSample d) (Vec d) (finiteHistorySigma Δ n) inferInstance
      (fun z => (Probability.stoppedHistorySample Δ n z).1 0) at h
    simpa only [Probability.stoppedHistorySample_path Δ n _ 0 zero_le] using h
  have hG : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance G :=
    Measurable.ite ((measurableSet_eq_fun hzero measurable_const).inter
      (measurableSet_noBacktracking_prefix Δ n R i))
      (hF.mono (finiteHistorySigma_mono Δ hmn) le_rfl) measurable_const
  obtain ⟨C, hbC⟩ := hb
  have hbG : BoundedRealTest G := by
    refine ⟨max C 0, fun z => ?_⟩
    dsimp only [G]
    split_ifs
    · exact (hbC z).trans (le_max_left _ _)
    · simpa only [abs_zero] using (le_max_right C 0)
  have hsG : ∀ z, G z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R ≤ z.1 t i := by
    intro z hz t ht
    have hzcond : z.1 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ →
        -R < z.1 t i - z.1 0 i := by
      by_contra h
      exact hz (ite_eq_right h)
    have h := hzcond.2 t ht
    rw [hzcond.1] at h
    simpa only [Pi.zero_apply, sub_zero] using h.le
  have hcomp := sbxTakeoverMinimalR01_future_histories_eq_of_stopped_map_eq_phys hd Λ₀ hΛ₀ lam h0 h1
    Δ hΔ δ R hR i P K ω ω' hg hg' hstop 0 hg.2.1 hg'.2.1 n hn G hG hbG hsG
  have hchange : ∀ η : FieldPair d,
      CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K η →
      (∫ z, G z ∂K (0, η)) = ∫ z,
        (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
          then F z else 0) ∂K (0, η) := by
    intro η hη
    obtain ⟨_, r, hr⟩ := hη.1
    have hs := r.pathLaw_starts_at 0
    rw [← hr 0, ← hη.2.1.2.1] at hs
    apply integral_congr_ae
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hs] with z hz
    change z.1 0 = 0 at hz
    simp only [G, hz, true_and]
  rw [hchange ω hg, hchange ω' hg'] at hcomp
  exact hcomp

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxTakeoverMinimalR01_future_raw_finite_history_eq_of_stopped_map_eq`. -/
theorem sbxTakeoverMinimalR01_future_raw_finite_history_eq_of_stopped_map_eq_phys
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
    (hstop : ∀ y : Vec d, -R ≤ y i →
      (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}))
    (n : ℕ) (hn : 1 ≤ n) :
    sbxS8FiniteKilledHistory (K (0, ω)) Δ R i n =
      sbxS8FiniteKilledHistory (K (0, ω')) Δ R i n := by
  let : IsProbabilityMeasure (K (0, ω)) := hg.2.1.1
  let : IsProbabilityMeasure (K (0, ω')) := hg'.2.1.1
  apply Measure.ext
  intro E hE
  let A := (Probability.stoppedHistorySample Δ n) ⁻¹' E
  have hA : MeasurableSet[finiteHistorySigma Δ n] A :=
    (Probability.measurable_stoppedHistorySample Δ n) hE
  have hAm : MeasurableSet A := Probability.finiteHistorySigma_le Δ n A hA
  have hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance
      (A.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hA
  have hb : BoundedRealTest (A.indicator fun _ => (1 : ℝ)) :=
    ⟨1, fun z => by by_cases hz : z ∈ A <;> simp [hz]⟩
  have hint := sbxTakeoverMinimalR01_future_finite_barrier_eq_of_stopped_map_eq_phys hd Λ₀ hΛ₀ lam h0 h1
    Δ hΔ δ R hR i P K ω ω' hg hg' hstop n n le_rfl hn _ hF hb
  have hconv : ∀ μ : Measure (CoupledSample d),
      (∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
        then (A.indicator fun _ => (1 : ℝ)) z else 0) ∂μ) =
        μ.real (sbxS8FutureBarrier Δ R i n ∩ A) := by
    intro μ
    have he : (fun z : CoupledSample d =>
        if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
        then (A.indicator fun _ => (1 : ℝ)) z else 0) =
        (sbxS8FutureBarrier Δ R i n ∩ A).indicator fun _ => (1 : ℝ) := by
      funext z
      by_cases hz : ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
      · by_cases ha : z ∈ A
        · rw [ite_eq_left hz, Set.indicator_of_mem ha,
            Set.indicator_of_mem (show z ∈ sbxS8FutureBarrier Δ R i n ∩ A from ⟨hz, ha⟩)]
        · rw [ite_eq_left hz, Set.indicator_of_notMem ha,
            Set.indicator_of_notMem (show z ∉ sbxS8FutureBarrier Δ R i n ∩ A from fun h => ha h.2)]
      · rw [ite_eq_right hz,
          Set.indicator_of_notMem (show z ∉ sbxS8FutureBarrier Δ R i n ∩ A from fun h => hz h.1)]
    rw [he, integral_indicator_const (1 : ℝ)
      ((sbxS8_measurableSet_futureBarrier Δ R i n).inter hAm)]
    simp
  rw [hconv, hconv] at hint
  have heq := (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (K (0, ω)) _)
    (measure_ne_top (K (0, ω')) _)).1 hint
  simp only [sbxS8FiniteKilledHistory, Measure.map_apply
    (sbxS8_measurable_stoppedHistorySample Δ n) hE]
  change (K (0, ω)).restrict (sbxS8FutureBarrier Δ R i n) A =
    (K (0, ω')).restrict (sbxS8FutureBarrier Δ R i n) A
  rw [Measure.restrict_apply hAm, Measure.restrict_apply hAm]
  simpa only [Set.inter_comm] using heq

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxTakeoverMinimalR01_s3_finite_killed_history_of_requested_locality`. -/
theorem sbxTakeoverMinimalR01_s3_finite_killed_history_of_requested_locality_phys (requested_s3_future_supplied_stopped_locality : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (_hl : 0 < l) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (_hK : Renewal.IsGMPCouplingV2Phys hd hΛ₀ Q lam l δ h0.le h1 P K), let R := l / lam; let i := Renewal.forceCoord hd; let _Δ := Renewal.regenDelta lam; ∀ (ω ω' : FieldPair d) (hω : IsRegular (sourceReducedBound Λ₀) ω) (hω' : IsRegular (sourceReducedBound Λ₀) ω') (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) ω hω lam h0.le h1) (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) ω' hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y) → (∀ y : Vec d, P (y, ω') = r'.pathLaw y) → (∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → ∀ y : Vec d, -R ≤ y i → (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) = (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i})) : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (_hl : 0 < l) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (_hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K), ∀ n : ℕ, ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂ProbabilityTheory.condExpKernel Q.measure (localSigma {x : Vec d | -2 * (l / lam) ≤ x (Regeneration.Renewal.forceCoord hd)}) ω, sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel (l / lam) (Regeneration.Renewal.forceCoord hd) K ω) (Regeneration.Renewal.regenDelta lam) (l / lam) (Regeneration.Renewal.forceCoord hd) n = sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel (l / lam) (Regeneration.Renewal.forceCoord hd) K ω') (Regeneration.Renewal.regenDelta lam) (l / lam) (Regeneration.Renewal.forceCoord hd) n := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl P K hK n
  by_cases hn : n = 0
  · subst n
    exact sbxTakeoverMinimalR01_s3_finite_killed_history_zero_phys hd Q lam h0 h1 l δ hl P K hK
  have hn' : 1 ≤ n := by omega
  let R := l / lam
  let i := Renewal.forceCoord hd
  let Δ := Renewal.regenDelta lam
  let m := localSigma {x : Vec d | -2 * R ≤ x i}
  let : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hR : 0 < R := div_pos hl h0
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  have hm := Probability.localSigma_le_borel {x : Vec d | -2 * R ≤ x i}
  have hg := ae_coupledEnvironmentRegular_phys hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 Δ hΔ δ R i hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  have hc0 : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
      CoupledEnvironmentRegularPhys hd Λ₀ Q.ellipticity_parameter lam h0.le h1 Δ δ R i P K ω' := by
    rw [condExpKernel_comp_trim hm]
    exact hg
  have hc := ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hc0)
  have hf := sbxTakeoverMinimalR01_resampling_fields_eq_on Q.measure {x : Vec d | -2 * R ≤ x i}
  have ht : ∀ᵐ ω ∂Q.measure,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
        sbxS8FiniteKilledHistory (K (0, ω)) Δ R i n := by
    filter_upwards [hK.1.1,
      future_locality_ae_starts_at_origin_of_coupling_phys hd Q lam l δ h0.le h1 P K hK]
      with ω hp hs
    have : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    rw [sbxS2StoppedOriginKernel, Kernel.map_apply _ (sbxS2_measurable_stopFutureSample R i),
      Probability.probabilityPart_eq_of_isProbabilityMeasure]
    exact sbxTakeoverMinimalR01_future_finite_history_stop_transport (K (0, ω)) Δ R hR i n hs
  have htc0 : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i n =
        sbxS8FiniteKilledHistory (K (0, ω')) Δ R i n := by
    rw [condExpKernel_comp_trim hm]
    exact ht
  have htc := ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp htc0)
  filter_upwards [hg, hc, hf, ht, htc] with ω hω hc hf ht htc
  filter_upwards [hc, hf, htc] with ω' hω' heq ht'
  obtain ⟨hreg, r, hr⟩ := hω.1
  obtain ⟨hreg', r', hr'⟩ := hω'.1
  have hstop := requested_s3_future_supplied_stopped_locality hd Q.ellipticity_parameter
    Q lam l δ hl h0 h1 P K hK ω ω' hreg hreg' r r' hr hr'
    (fun y hy => heq y hy)
  rw [ht, ht']
  exact sbxTakeoverMinimalR01_future_raw_finite_history_eq_of_stopped_map_eq_phys hd Λ₀ Q.ellipticity_parameter
    lam h0.le h1 Δ hΔ δ R hR i P K ω ω' hω hω' hstop n hn'

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxTakeoverR01_future_kernel`. -/
theorem sbxTakeoverR01_future_kernel_phys :
    node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys := by
  apply sbxTakeoverMinimalR01_future_kernel_of_finite_histories_phys
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl _ _ _ P K hK
  exact sbxTakeoverMinimalR01_s3_finite_killed_history_of_requested_locality_phys
    EinsteinFull.s2_future_supplied_stopped_locality_phys hd Q lam h0 h1 l δ hl P K hK

end EinsteinFull.Blueprint
