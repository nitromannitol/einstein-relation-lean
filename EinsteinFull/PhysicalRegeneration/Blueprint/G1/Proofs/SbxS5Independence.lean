import EinsteinFull.Blueprint.G1.Proofs.SbxS5Independence
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS5Independence`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory Classical
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration
section Setup
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
include hK hl hsep hδ₀ hδ₁
/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_firstSlicePast_local`. -/
theorem sbxS5_firstSlicePast_local_phys
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H) (y : Vec d) :
    ∃ A' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d |
        x (Renewal.forceCoord hd) ≤ y (Renewal.forceCoord hd) - 4 * (l / lam)}] A' ∧
      (fun ω => firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) m K H (y, ω)) =ᵐ[Q.measure] A' := by
  classical
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h₀
  have hR : 0 < R := div_pos hl h₀
  let Γ := forcedBitTrialEvent Δ lam R i m
  let E : Set (CoupledSample d) := {z | y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))}
  let J := E.indicator (Γ.indicator H)
  have hJ : Measurable[finiteHistorySigma Δ m] J :=
    (hH.indicator (measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i m)).indicator
      (measurableSet_endpointBall_past Δ R i m y)
  have hbJ : BoundedRealTest J := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · by_cases hΓ : z ∈ Γ
      · simpa only [J, Set.indicator_of_mem hz, Set.indicator_of_mem hΓ] using
          (hC z).trans (le_max_left C 0)
      · simpa only [J, Set.indicator_of_mem hz, Set.indicator_of_notMem hΓ, abs_zero] using
          (le_max_right C 0)
    · simpa only [J, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
  have hbar : ∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ y i - 7 * R) →
      J z = 0 := by
    intro z hz
    by_cases he : z ∈ E
    · by_cases hΓ : z ∈ Γ
      · exact (hz (forcedBitTrialEvent_endpoint_past_barrier Δ hΔ lam R h₀ hR i m z
          hΓ y he)).elim
      · simp only [J, Set.indicator_of_mem he, Set.indicator_of_notMem hΓ]
    · exact Set.indicator_of_notMem he _
  obtain ⟨A', hA', heq⟩ := hpast d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK m (y i - 7 * R) J hJ hbJ hbar
  have hv : y i - 7 * R + 3 * R = y i - 4 * R := by ring
  rw [hv] at hA'
  refine ⟨A', hA', ?_⟩
  have hident : (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q.measure]
      (fun ω => ∫ z, J z ∂K (0, ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    by_cases he : z ∈ E
    · change y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) at he
      simp only [J, E, Γ, Set.indicator, Set.mem_ofPred_eq, he, ite_true, mul_one]
    · change y ∉ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) at he
      simp only [J, E, Set.indicator, Set.mem_ofPred_eq, he, ite_false, mul_zero]
  exact hident.trans heq

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_firstSlicePast_zero`. -/
theorem sbxS5_firstSlicePast_zero_phys
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ) (y : Vec d)
    (hy : y (Renewal.forceCoord hd) < 10 * (l / lam)) :
    (fun ω => firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) =ᵐ[Q.measure] 0 := by
  classical
  have hstart := ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1
  have hstartK := ae_quenched_of_annealed Q.measure K hK.1 hstart
  have hgeom := (hslices d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK n hn).2.2
  filter_upwards [hstartK] with ω hω
  apply integral_eq_zero_of_ae
  filter_upwards [hω] with z hz
  by_cases hΓ : z ∈ forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1)
  · have hb : y ∉ endpointBall (Renewal.forceCoord hd) (l / lam)
        (z.1 (((n - 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) := by
      intro hb
      exact (not_le.mpr hy) ((hgeom z hz hΓ).2.2 y hb).1
    simp only [Set.indicator_of_mem hΓ, ite_eq_right hb, mul_zero, Pi.zero_apply]
  · simp only [Set.indicator_of_notMem hΓ, zero_mul, Pi.zero_apply]

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_pastFactor_local`. -/
theorem sbxS5_pastFactor_local_phys
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H) (y : Vec d)
    (hy : 10 * (l / lam) ≤ y (Renewal.forceCoord hd)) :
    ∃ A' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d |
        x (Renewal.forceCoord hd) ≤ y (Renewal.forceCoord hd) - 4 * (l / lam)}] A' ∧
      (fun ω => F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) m K H (y, ω)) =ᵐ[Q.measure] A' := by
  obtain ⟨A', hA', heq⟩ := sbxS5_firstSlicePast_local_phys hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hpast m H hH hbH y
  have hFlocal : Measurable[localSigma {x : Vec d |
      x (Renewal.forceCoord hd) ≤ y (Renewal.forceCoord hd) - 4 * (l / lam)}] F := by
    apply hF.mono (Probability.localSigma_mono ?_) le_rfl
    intro x hx
    have hcoord := (le_abs_self (x (Renewal.forceCoord hd))).trans
      (coordinate_abs_le_euclideanNorm x (Renewal.forceCoord hd))
    have hR := div_pos hl h₀
    change euclideanNorm x < l / lam at hx
    change x (Renewal.forceCoord hd) ≤ y (Renewal.forceCoord hd) - 4 * (l / lam)
    linarith
  exact ⟨fun ω => F ω * A' ω, hFlocal.mul hA', (Filter.EventuallyEq.rfl).mul heq⟩

omit hl hsep hδ₀ hδ₁ in
/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_killedFuture_origin_mean`. -/
theorem sbxS5_killedFuture_origin_mean_phys
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z)
      ∂K (0, ω) ∂Q.measure) =
      (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  exact integral_killed_future_origin_eq_condIntegral Q.measure K hK.1
    (ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h₀.le h₁ P K
      hK.1 hK.2.1 hK.2.2.1)
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) hD Φ hΦ hbΦ
    (fun yω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ (yω, z) ∂K yω)
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_firstMarginal_of_sliceIdentity`. -/
theorem sbxS5_firstMarginal_of_sliceIdentity_phys
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (hslice : ∀ n : ℕ, 2 ≤ n →
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
      (∫ _q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        (1 : ℝ) ∂annealedCoupledLaw Q.measure K) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) :
    (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hsc := hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1
  have hgrid := hsc.2.2 μ (by simp [μ])
  let s : ℕ → Set (FieldPair d × CoupledSample d) := fun n =>
    {q | regenerationTime hd lam l 1 q.2 =
      ((((n + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs (n : ℕ) : MeasurableSet (s n) :=
    (hsc.1.comp measurable_snd) (measurableSet_singleton _)
  have hdis : Pairwise (fun m n => Disjoint (s m) (s n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro q hm hn
    have he := ENNReal.coe_inj.mp (hm.symm.trans hn)
    have hc := mul_right_cancel₀ (EinsteinRelation.regenDelta_pos h₀).ne' he
    have hnat : m + 2 = n + 2 := by exact_mod_cast hc
    exact hmn (Nat.add_right_cancel hnat)
  have hcover : ∀ᵐ q ∂μ, q ∈ ⋃ n, s n := by
    filter_upwards [hgrid] with q hq
    obtain ⟨n, hn, ht, _⟩ := hq
    have hn₂ : n - 2 + 2 = n := by omega
    refine Set.mem_iUnion.mpr ⟨n - 2, ?_⟩
    change regenerationTime hd lam l 1 q.2 =
      ((((n - 2 + 2 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)
    simpa only [hn₂] using ht
  have hseries (f : FieldPair d × CoupledSample d → ℝ) (hf : Integrable f μ) :
      HasSum (fun n => ∫ q in s n, f q ∂μ) (∫ q, f q ∂μ) := by
    have h := hasSum_integral_iUnion hs hdis hf.integrableOn
    rw [Measure.restrict_eq_self_of_ae_mem hcover] at h
    exact h
  have hb : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) μ := by
    obtain ⟨C, hC⟩ := hbΦ
    exact Integrable.of_bound (hΦ.comp hsc.2.1).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  have hleft := hseries _ hb
  let c := ∫ q, Φ (regenerationRecord hd lam l 0 q)
    ∂regenerationConditionedLaw hd Q lam l K hK.1 hD
  have hright := (hseries (fun _ => (1 : ℝ)) (integrable_const 1)).mul_right c
  have heq : (fun n => ∫ q in s n, Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      (fun n => (∫ q in s n, (1 : ℝ) ∂μ) * c) := by
    funext n
    exact hslice (n + 2) (by omega)
  rw [heq] at hleft
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] using
    hleft.unique hright

end Setup
section ShiftedOrigin
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
include hK hl hsep hδ₀ hδ₁
/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_shiftedOriginFuture_local_mean`. -/
theorem sbxS5_shiftedOriginFuture_local_mean_phys
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) (y : Vec d) :
    ∃ B' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d |
        y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ x (Renewal.forceCoord hd)}] B' ∧
      (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)) =ᵐ[Q.measure] B' ∧
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω) ∂Q.measure) =
        ∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
          ((0, ω), z) ∂K (0, ω) ∂Q.measure := by
  obtain ⟨B, hB, hBo⟩ :=
    hfuture d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK Φ hΦ hbΦ
  have hmap : ∀ᵐ ω ∂Measure.map (translate y) Q.measure,
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, ω), z) ∂K (0, ω)) = B ω := by
    rw [Q.stationary y]
    exact hBo
  have ht := ae_of_ae_map (Probability.measurable_translate y).aemeasurable hmap
  refine ⟨fun ω => B (translate y ω), ?_, ht, ?_⟩
  · apply (hB.comp (Probability.measurable_translate_local y _)).mono
      (Probability.localSigma_mono ?_) le_rfl
    rintro x ⟨z, hz, rfl⟩
    change -2 * (l / lam) ≤ z (Renewal.forceCoord hd) at hz
    change y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ (y + z) (Renewal.forceCoord hd)
    simp only [Pi.add_apply]
    linarith
  · have hBg : Measurable B := hB.mono (Probability.localSigma_le_borel _) le_rfl
    rw [integral_congr_ae ht,
      ← integral_map (Probability.measurable_translate y).aemeasurable hBg.aestronglyMeasurable,
      Q.stationary y]
    exact integral_congr_ae hBo.symm

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS5_firstSlicePast_shiftedOriginFuture_factorization`. -/
theorem sbxS5_firstSlicePast_shiftedOriginFuture_factorization_phys
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H) (y : Vec d)
    (hy : 10 * (l / lam) ≤ y (Renewal.forceCoord hd)) :
    (∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) m K H (y, ω)) *
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure) =
      (∫ ω, F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) m K H (y, ω) ∂Q.measure) *
      ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  obtain ⟨A', hA', hAe⟩ := sbxS5_pastFactor_local_phys hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hpast F hF m H hH hbH y hy
  obtain ⟨B', hB', hBe, hmean⟩ := sbxS5_shiftedOriginFuture_local_mean_phys
    hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hfuture Φ hΦ hbΦ y
  rw [integral_mul_eq_of_corrected_halfSpace_versions Q (Renewal.forceCoord hd)
    (y (Renewal.forceCoord hd)) (l / lam) (sbxS5_radius_gap hl h₀ h₁ hsep)
    _ _ A' B' hA' hB' hAe hBe, hmean,
    sbxS5_killedFuture_origin_mean_phys hd Q lam h₀ h₁ l δ P K hK hD Φ hΦ hbΦ]

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS5_firstSlicePast_shiftedOriginFuture_spatial_integral`. -/
theorem sbxS5_firstSlicePast_shiftedOriginFuture_spatial_integral_phys
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    (∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure) =
      ((volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal *
        ∫ q, F q.1 * ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
            ∂annealedCoupledLaw Q.measure K) *
      ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
  let A : Vec d → FieldPair d → ℝ := fun y ω => F ω *
    firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) (n - 1) K H (y, ω)
  let B : Vec d → FieldPair d → ℝ := fun y ω =>
    ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
      ((0, translate y ω), z) ∂K (0, translate y ω)
  let c := (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
    ∫ q, Φ (regenerationRecord hd lam l 0 q)
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD
  have heq : ∀ y, (∫ ω, A y ω * B y ω ∂Q.measure) =
      (∫ ω, A y ω ∂Q.measure) * c := by
    intro y
    by_cases hy : 10 * (l / lam) ≤ y (Renewal.forceCoord hd)
    · exact sbxS5_firstSlicePast_shiftedOriginFuture_factorization_phys
        hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hpast hfuture hD
        Φ hΦ hbΦ F hF (n - 1) H hH hbH y hy
    · have hAz : A y =ᵐ[Q.measure] 0 := by
        filter_upwards [sbxS5_firstSlicePast_zero_phys hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
          P K hK hslices n hn H y (lt_of_not_ge hy)] with ω hω
        simp only [Pi.zero_apply] at hω ⊢
        change F ω * _ = 0
        rw [hω, mul_zero]
      have hA0 : (∫ ω, A y ω ∂Q.measure) = 0 := integral_eq_zero_of_ae hAz
      have hAB0 : (∫ ω, A y ω * B y ω ∂Q.measure) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hAz] with ω hω
        simp only [Pi.zero_apply] at hω ⊢
        rw [hω, zero_mul]
      rw [hA0, hAB0, zero_mul]
  calc
    _ = ∫ y, (∫ ω, A y ω ∂Q.measure) * c := integral_congr_ae
      (Filter.Eventually.of_forall heq)
    _ = (∫ y, ∫ ω, A y ω ∂Q.measure) * c := integral_mul_const _ _
    _ = _ := congrArg (fun t => t * c)
      (sbxS5_firstSlicePastFactor_spatial_integral Q.measure K hK.1
        (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) (div_pos hl h₀)
        (n - 1) F (hF.mono (Probability.localSigma_le_borel _) le_rfl) hbF H
        (hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl) hbH)

end ShiftedOrigin
section EndpointDifference
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
include hK hl hsep hδ₀ hδ₁
/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS5_firstSlicePast_killedFuture_spatial_difference`. -/
theorem sbxS5_firstSlicePast_killedFuture_spatial_difference_phys
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    let A := fun (y : Vec d) (ω : FieldPair d) => F ω *
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    (∫ y, ∫ ω, A y ω * B y ω ∂Q.measure) =
      ((volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal *
        ∫ q, F q.1 * ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
            ∂annealedCoupledLaw Q.measure K) *
      ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) +
      ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by
  intro A B B₀
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hHg : Measurable H := hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl
  have hi := sbxS5_integrable_firstSlicePast_killedFuture Q.measure K hK.1
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) (div_pos hl h₀)
    (n - 1) F hFg hbF H hHg hbH Φ hΦ hbΦ
  have hi₀ := sbxS5_integrable_firstSlicePast_shiftedOriginFuture Q.measure Q.stationary
    K hK.1 (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) (div_pos hl h₀)
    (n - 1) F hFg hbF H hHg hbH Φ hΦ hbΦ
  have hdiff : (∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure) =
      (∫ y, ∫ ω, A y ω * B y ω ∂Q.measure) -
      ∫ y, ∫ ω, A y ω * B₀ y ω ∂Q.measure := by
    simpa only [mul_sub] using integral_integral_sub hi hi₀
  calc
    _ = (∫ y, ∫ ω, A y ω * B₀ y ω ∂Q.measure) +
        ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by rw [hdiff]; ring
    _ = _ := by
      rw [sbxS5_firstSlicePast_shiftedOriginFuture_spatial_integral_phys
        hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hpast hfuture hslices hD
        Φ hΦ hbΦ F hF hbF n hn H hH hbH]

end EndpointDifference
/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS5_endpointDisintegration_fullFuture`. -/
theorem sbxS5_endpointDisintegration_fullFuture_phys
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K) =
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
            (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
              ((y, ω), z) ∂K (y, ω)) ∂Q.measure := by
  classical
  let R := l / lam
  let i := Renewal.forceCoord hd
  let c := δ / (volume (endpointBall i R (0 : Vec d))).toReal
  let μ := annealedCoupledLaw Q.measure K
  let ρ := μ.restrict {q | regenerationTime hd lam l 1 q.2 =
    (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  let σ := (volume : Measure (Vec d)).prod Q.measure
  let η := σ.compProd (Probability.probabilityPart K)
  let A := fun p : Vec d × FieldPair d => F p.2 *
    firstSlicePastIntegral (Renewal.regenDelta lam) lam R i (n - 1) K H p
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hHg : Measurable H := hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl
  have hiA : Integrable A σ := sbxS5_integrable_firstSlicePastFactor Q.measure K hK.1
    (Renewal.regenDelta lam) lam R i (div_pos hl h₀) (n - 1) F hFg hbF H hHg hbH
  let A' := hiA.aestronglyMeasurable.mk A
  have hA' : Measurable A' := hiA.aestronglyMeasurable.measurable_mk
  have heqA : A =ᵐ[σ] A' := hiA.aestronglyMeasurable.ae_eq_mk
  have hiA' : Integrable A' σ := hiA.congr heqA
  let T := fun p : (Vec d × FieldPair d) × CoupledSample d =>
    spatialFutureRecord R i p.1 p.2
  have hT : Measurable T := measurable_spatial_future_triple R i
  let v := fun p : (Vec d × FieldPair d) × CoupledSample d =>
    (c * A' p.1) * killedFutureTest R i (fun _ => 1) p
  have hv : Measurable v :=
    (measurable_const.mul (hA'.comp measurable_fst)).mul
      (measurable_killedFutureTest R i (fun _ => 1) measurable_const)
  have hiv : Integrable v η := by
    apply ((sbxS5_integrable_kernelLift σ K hK.1.2 A' hA' hiA').const_mul c).mul_bdd (c := 1)
      (measurable_killedFutureTest R i (fun _ => 1) measurable_const).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      dsimp only [killedFutureTest]
      split_ifs <;> norm_num
  have hspatial : ∀ (ψ : FutureState d i R → ℝ), Measurable ψ → BoundedRealTest ψ →
      (∫ p, v p * ψ (T p) ∂η) =
        c * ∫ y, ∫ ω, A (y, ω) * (∫ z, killedFutureTest R i ψ ((y, ω), z)
          ∂K (y, ω)) ∂Q.measure := by
    intro ψ hψ hbψ
    calc
      (∫ p, v p * ψ (T p) ∂η) =
          c * ∫ p, A' p.1 * killedFutureTest R i ψ p ∂η := by
        rw [← integral_const_mul]
        congr 1
        funext p
        dsimp only [v, T, killedFutureTest]
        split_ifs <;> ring
      _ = c * ∫ p, A' p * (∫ z, killedFutureTest R i ψ (p, z) ∂K p) ∂σ := by
        rw [sbxS5_signedWeight_kernel_integral σ K hK.1.2 A' hA' hiA'
          (killedFutureTest R i ψ) (measurable_killedFutureTest R i ψ hψ)
          (boundedRealTest_killedFutureTest R i ψ hbψ)]
      _ = c * ∫ p, A p * (∫ z, killedFutureTest R i ψ (p, z) ∂K p) ∂σ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [heqA] with p hp
        rw [hp]
      _ = _ := by
        dsimp only [σ, A]
        rw [integral_prod _ (sbxS5_integrable_firstSlicePast_killedFuture Q.measure K hK.1
          (Renewal.regenDelta lam) lam R i (div_pos hl h₀) (n - 1)
          F hFg hbF H hHg hbH ψ hψ hbψ)]
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let W := fun q : FieldPair d × CoupledSample d => F q.1 * H q.2
  have hW : Measurable W := (hFg.comp measurable_fst).mul (hHg.comp measurable_snd)
  have hiW : Integrable W ρ := by
    obtain ⟨CF, hCF⟩ := hbF
    obtain ⟨CH, hCH⟩ := hbH
    apply Integrable.of_bound hW.aestronglyMeasurable (max CF 0 * max CH 0)
    exact Filter.Eventually.of_forall fun q => by
      simp only [W, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul ((hCF _).trans (le_max_left _ _))
        ((hCH _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hrecord := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1).2.1
  have htest : ∀ (f : Path d × BernoulliSequence → ℝ), Measurable f → BoundedRealTest f →
      ∀ (g : (FutureHalfSpace d i R → Mat d × ℝ) → ℝ), Measurable g → BoundedRealTest g →
      (∫ q, W q * (f ((regenerationRecord hd lam l 1 q).1,
        (regenerationRecord hd lam l 1 q).2.1) * g (regenerationRecord hd lam l 1 q).2.2) ∂ρ) =
      ∫ p, v p * (f ((T p).1, (T p).2.1) * g (T p).2.2) ∂η := by
    intro f hf hbf g hg hbg
    let ψ : FutureState d i R → ℝ := fun r => f (r.1, r.2.1) * g r.2.2
    have hψ : Measurable ψ :=
      (hf.comp (measurable_fst.prodMk measurable_snd.fst)).mul
        (hg.comp measurable_snd.snd)
    have hbψ : BoundedRealTest ψ := by
      obtain ⟨Cf, hCf⟩ := hbf
      obtain ⟨Cg, hCg⟩ := hbg
      refine ⟨max Cf 0 * max Cg 0, fun r => ?_⟩
      simp only [ψ, abs_mul]
      exact mul_le_mul ((hCf _).trans (le_max_left _ _))
        ((hCg _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    change (∫ q, W q * ψ (regenerationRecord hd lam l 1 q) ∂ρ) = ∫ p, v p * ψ (T p) ∂η
    rw [hspatial ψ hψ hbψ]
    exact hendpoint d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
      F hF hbF n hn H hH hbH f hf hbf g hg hbg
  have ht := sbxS5_signedWeighted_futureTests i R ρ η W v hW hv hiW hiv
    (regenerationRecord hd lam l 1) T hrecord hT htest Φ hΦ hbΦ
  rw [hspatial Φ hΦ hbΦ] at ht
  exact ht

section CenteredEndpointDifference
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
include hK hl hsep hδ₀ hδ₁
/-- The physical-kernel version of `EinsteinFull.Blueprint.sbxS5_fullSlice_endpoint_difference`. -/
theorem sbxS5_fullSlice_endpoint_difference_phys
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let A := fun (y : Vec d) (ω : FieldPair d) => F ω *
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K) =
      δ * (∫ q, F q.1 * ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
            ∂annealedCoupledLaw Q.measure K) *
        ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
          ∫ q, Φ (regenerationRecord hd lam l 0 q)
            ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) +
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by
  intro A B B₀
  have hV : (volume (endpointBall (Renewal.forceCoord hd) (l / lam) (0 : Vec d))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr
      ⟨(endpointBall_volume_pos _ _ (div_pos hl h₀) _).ne',
        endpointBall_volume_ne_top _ _ (div_pos hl h₀) _⟩
  rw [sbxS5_endpointDisintegration_fullFuture_phys hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hendpoint hscope hD F hF hbF n hn H hH hbH Φ hΦ hbΦ]
  rw [sbxS5_firstSlicePast_killedFuture_spatial_difference_phys
    hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hpast hfuture hslices hD
    Φ hΦ hbΦ F hF hbF n hn H hH hbH]
  field_simp
  ring

/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS5_sliceIndependence_centered_remainder`. -/
theorem sbxS5_sliceIndependence_centered_remainder_phys
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let m := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    let Ψ := fun r => Φ r - m
    let A := fun (y : Vec d) (ω : FieldPair d) => F ω *
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ ((y, ω), z) ∂K (y, ω)
    let B₀ := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
        ((0, translate y ω), z) ∂K (0, translate y ω)
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂μ) -
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 * H q.2 ∂μ) * m =
      (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0)).toReal) *
        ∫ y, ∫ ω, A y ω * (B y ω - B₀ y ω) ∂Q.measure := by
  intro μ ν m Ψ A B B₀
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hD
  have hΨ : Measurable Ψ := hΦ.sub measurable_const
  obtain ⟨C, hC⟩ := hbΦ
  have hbΨ : BoundedRealTest Ψ :=
    ⟨C + |m|, fun r => (abs_sub (Φ r) m).trans (by linarith only [hC r])⟩
  have hrecord₀ := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 0).2.1
  have hiΦ₀ : Integrable (fun q => Φ (regenerationRecord hd lam l 0 q)) ν :=
    Integrable.of_bound (hΦ.comp hrecord₀).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  have hmean : (∫ q, Ψ (regenerationRecord hd lam l 0 q) ∂ν) = 0 := by
    rw [show (fun q => Ψ (regenerationRecord hd lam l 0 q)) =
      (fun q => Φ (regenerationRecord hd lam l 0 q) - m) from rfl]
    rw [integral_sub hiΦ₀ (integrable_const m)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul, m, sub_self]
  let ρ := μ.restrict {q | regenerationTime hd lam l 1 q.2 =
    (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  let W := fun q : FieldPair d × CoupledSample d => F q.1 * H q.2
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hHg : Measurable H := hH.mono (Probability.finiteHistorySigma_le _ _) le_rfl
  have hW : Measurable W := (hFg.comp measurable_fst).mul (hHg.comp measurable_snd)
  obtain ⟨CF, hCF⟩ := hbF
  obtain ⟨CH, hCH⟩ := hbH
  have hiW : Integrable W ρ := by
    apply Integrable.of_bound hW.aestronglyMeasurable (max CF 0 * max CH 0)
    exact Filter.Eventually.of_forall fun q => by
      simp only [W, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul ((hCF _).trans (le_max_left _ _))
        ((hCH _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hrecord₁ := (hscope d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD 1).2.1
  have hiWΦ : Integrable (fun q => W q * Φ (regenerationRecord hd lam l 1 q)) ρ :=
    hiW.mul_bdd (hΦ.comp hrecord₁).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC _)
  have hcenter : (∫ q, W q * Ψ (regenerationRecord hd lam l 1 q) ∂ρ) =
      (∫ q, W q * Φ (regenerationRecord hd lam l 1 q) ∂ρ) -
        (∫ q, W q ∂ρ) * m := by
    simp only [Ψ, mul_sub]
    rw [integral_sub hiWΦ (hiW.mul_const m), integral_mul_const]
  have heq := sbxS5_fullSlice_endpoint_difference_phys hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
    P K hK hendpoint hpast hfuture hslices hscope hD F hF ⟨CF, hCF⟩ n hn H hH
    ⟨CH, hCH⟩ Ψ hΨ hbΨ
  rw [hmean] at heq
  change (∫ q, W q * Φ (regenerationRecord hd lam l 1 q) ∂ρ) -
    (∫ q, W q ∂ρ) * m = _
  rw [← hcenter]
  simpa only [mul_zero, zero_add] using heq

end CenteredEndpointDifference
section FirstCycleRemainderSeries
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
include hK hl hsep hδ₀ hδ₁
end FirstCycleRemainderSeries
end EinsteinFull.Blueprint
