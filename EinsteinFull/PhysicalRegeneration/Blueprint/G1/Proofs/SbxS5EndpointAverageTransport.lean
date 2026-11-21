import EinsteinFull.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5Independence
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint.EndpointAverageTransport
open EinsteinRelation EinsteinRelation.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Blueprint.EndpointAverageTransport.killed_future_origin_eq_frozen_record`. -/
theorem killed_future_origin_eq_frozen_record_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0 h1 P K)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, ω), z)
      ∂K (0, ω) ∂Q.measure) =
    ∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
      ∂annealedCoupledLaw Q.measure K := by
  classical
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ ((0, q.1), q.2)
  have hF : Measurable F :=
    (measurable_killedFutureTest _ _ Φ hΦ).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hbF : BoundedRealTest F := by
    obtain ⟨C, hC⟩ := boundedRealTest_killedFutureTest _ _ Φ hb
    exact ⟨C, fun q => hC _⟩
  have hD : MeasurableSet (regenerationNoReturn hd (l / lam)) :=
    (measurableSet_NoBacktracking _ _).preimage measurable_snd.fst
  rw [← integral_annealedCoupledLaw Q.measure K hK.1 F hF hbF,
    ← integral_indicator hD]
  apply integral_congr_ae
  filter_upwards [ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h0 h1 P K
    hK.1 hK.2.1 hK.2.2.1] with q hq
  have hr := spatialFutureRecord_origin_eq_iteratedRecord_zero
    (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) q.1 q.2 hq
  change spatialFutureRecord _ _ _ _ = regenerationRecord hd lam l 0 q at hr
  change (if NoBacktracking (l / lam) q.2.1 (Renewal.forceCoord hd) then
    Φ (spatialFutureRecord _ _ _ _) else 0) = _
  rw [hr]
  rfl

/-- The physical-kernel version of
`EinsteinFull.Blueprint.EndpointAverageTransport.coupling_origin_eq_recenter_assuming_path_laws`. -/
theorem coupling_origin_eq_recenter_assuming_path_laws_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      ((∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          P p = sbxS9RecenteredPathLaws P a p) →
      ∀ᵐ η ∂Q.measure, K (0, η) = sbxS9RecenteredCoupledLaws K a (0, η) := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos h0 2))
  have hg := ae_coupledEnvironmentRegular_phys hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  filter_upwards [sbxS5_seven_coupling_clauses_recenter_phys hd Q.ellipticity_parameter
    Q lam l δ h0.le h1 P K hK] with a ha
  intro hP
  obtain ⟨hp, hm, _, hr, _, _, ho⟩ := ha
  have hreg : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) (sbxS9RecenteredPathLaws P a)
        (sbxS9RecenteredCoupledLaws K a) p := by
    filter_upwards [hp.2, hm.2, hr.2, ho.2] with p hpp hmp hrp hop
    exact ⟨hpp, hmp, hrp, hop⟩
  have hsp := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := Q.measure)
      (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae
      (hreg.and hP.2))
  have htrans := (show MeasurePreserving (translate (-a)) Q.measure Q.measure from
    ⟨Probability.measurable_translate (-a), Q.stationary (-a)⟩).quasiMeasurePreserving.ae
      hK.2.2.1
  filter_upwards [hg, htrans, hp.1, hm.1, hr.1, ho.1, hP.1, hsp]
    with η hgη htη hpη hmη hrη hoη hPη hspη
  have hs : ∀ x, ∀ᵐ γ ∂P (x, η), γ 0 = x := by
    obtain ⟨_, r, heq⟩ := hgη.1
    intro x
    rw [heq x]
    exact r.pathLaw_starts_at x
  have hs' : ∀ x, ∀ᵐ γ ∂sbxS9RecenteredPathLaws P a (x, η), γ 0 = x := by
    apply path_starts_recenter
    obtain ⟨_, r, heq⟩ := htη
    intro x
    rw [heq x]
    exact r.pathLaw_starts_at x
  have hboth : ∀ᵐ x ∂(volume : Measure (Vec d)),
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P K (x, η) ∧
      CoupledFibreRegular (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) (sbxS9RecenteredPathLaws P a)
        (sbxS9RecenteredCoupledLaws K a) (x, η) ∧
      P (x, η) = sbxS9RecenteredPathLaws P a (x, η) := by
    filter_upwards [hgη.2.2.1, hspη] with x hx hx'
    exact ⟨hx, hx'.1, hx'.2⟩
  have := hgη.2.1.1
  have := hpη
  exact measure_eq_of_finite_history_integrals _ _ (Renewal.regenDelta lam) hΔ
    (sbxS9_finite_histories_eq_of_path_laws_eq _ hΔ δ (l / lam)
      (Renewal.forceCoord hd) P (sbxS9RecenteredPathLaws P a) K
      (sbxS9RecenteredCoupledLaws K a) 0 η hs hs' hgη.2.1
      ⟨hpη, hmη, hrη, hoη⟩ hPη hboth (fun n hn => hgη.2.2.2 n hn 0))

section SliceSummation
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
include hl hsep hδ0 hδ1 hK
end SliceSummation
section OriginalPathCovariance
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hP : ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p)
include hK hP
/-- The physical-kernel version of
`EinsteinFull.Blueprint.EndpointAverageTransport.killed_future_eq_shifted_origin_assuming_path_laws`. -/
theorem killed_future_eq_shifted_origin_assuming_path_laws_phys
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((y, ω), z) ∂K (y, ω)) =ᵐ[Q.measure]
      (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂K (0, translate y ω)) := by
  filter_upwards [coupling_origin_eq_recenter_assuming_path_laws_phys hd Q lam h0 h1
    l δ P K hK, hP] with y hy hPy
  have htranslate : MeasurePreserving (translate y) Q.measure Q.measure :=
    ⟨Probability.measurable_translate y, Q.stationary y⟩
  filter_upwards [htranslate.quasiMeasurePreserving.ae (hy hPy)] with ω hω
  have ht : translate (-y) (translate y ω) = ω := by
    rw [translate_add, neg_add_cancel, translate_zero]
  calc
    _ = ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((0, translate y ω), z) ∂sbxS9RecenteredCoupledLaws K y (0, translate y ω) := by
      rw [killed_future_integral_recenter, ht]
    _ = _ := by rw [← hω]

include hl hsep hδ0 hδ1
/-- The physical-kernel version of
`EinsteinFull.Blueprint.EndpointAverageTransport.killed_future_local_mean_assuming_path_laws`. -/
theorem killed_future_local_mean_assuming_path_laws_phys
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∃ B' : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ x (Renewal.forceCoord hd)}] B' ∧
        (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
          ((y, ω), z) ∂K (y, ω)) =ᵐ[Q.measure] B') ∧
      (∫ ω, ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Φ
        ((y, ω), z) ∂K (y, ω) ∂Q.measure) =
        ∫ q in regenerationNoReturn hd (l / lam), Φ (regenerationRecord hd lam l 0 q)
          ∂annealedCoupledLaw Q.measure K := by
  filter_upwards [killed_future_eq_shifted_origin_assuming_path_laws_phys hd Q lam h0 h1
    l δ P K hK hP Φ] with y hy
  obtain ⟨B', hB', hBe, hmean⟩ := sbxS5_shiftedOriginFuture_local_mean_phys hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hfuture Φ hΦ hbΦ y
  exact ⟨⟨B', hB', hy.trans hBe⟩,
    (integral_congr_ae hy).trans (hmean.trans
      (killed_future_origin_eq_frozen_record_phys hd Q lam h0.le h1 l δ P K hK Φ hΦ hbΦ))⟩

/-- The physical-kernel version of
`EinsteinFull.Blueprint.EndpointAverageTransport.weighted_slice_identity_assuming_path_laws`. -/
theorem weighted_slice_identity_assuming_path_laws_phys
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
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
        ∂annealedCoupledLaw Q.measure K) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 ∂annealedCoupledLaw Q.measure K) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let b := ∫ q, Φ (regenerationRecord hd lam l 0 q)
    ∂regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Ψ := fun r => Φ r - b
  apply sub_eq_zero.mp
  rw [sbxS5_sliceIndependence_centered_remainder_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK hendpoint hpast hfuture hslices hscope hD F hF hbF n hn H hH hbH Φ hΦ hbΦ]
  suffices hz : (∫ y, ∫ ω,
      (F ω * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω)) *
      ((∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ ((y, ω), z) ∂K (y, ω)) -
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
          ((0, translate y ω), z) ∂K (0, translate y ω)) ∂Q.measure) = 0 by
    exact mul_eq_zero_of_right _ hz
  apply integral_eq_zero_of_ae
  filter_upwards [killed_future_eq_shifted_origin_assuming_path_laws_phys hd Q lam h0 h1
    l δ P K hK hP Ψ] with y hy
  apply integral_eq_zero_of_ae
  filter_upwards [hy] with ω hω
  simp only [Pi.zero_apply]
  rw [hω, sub_self, mul_zero]

end OriginalPathCovariance
/-- The physical-kernel version of
`EinsteinFull.Blueprint.EndpointAverageTransport.independence_assuming_original_path_covariance`. -/
theorem independence_assuming_original_path_covariance_phys
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (_htails : node_app_u3A_regen_u2D_tailsStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys)
    (hcov : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)),
        (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          P p = sbxS9RecenteredPathLaws P a p) :
    node_app_u3A_factorization_u23_independenceStmtV2_phys := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  dsimp only
  intro Φ hΦ hbΦ
  have hP := hcov d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
  have hfuture_local := killed_future_local_mean_assuming_path_laws_phys hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK hP hfuture Φ hΦ hbΦ
  constructor
  · intro F hF hbF n hn H hH hbH
    refine ⟨sbxS5_radius_gap hl h0 h1 hsep, ?_, ?_, ?_, ?_⟩
    · exact ae_of_all _ fun y hy => by
        filter_upwards [sbxS5_firstSlicePast_zero_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
          P K hK hslices n hn H y hy] with ω hω
        simp only [Pi.zero_apply] at hω ⊢
        rw [hω, mul_zero]
    · filter_upwards [hfuture_local] with y hy
      intro hhigh
      obtain ⟨A', hA', hAe⟩ := sbxS5_pastFactor_local_phys hd Q lam h0 h1 l δ
        hl hsep hδ0 hδ1 P K hK hpast F hF (n - 1) H hH hbH y hhigh
      obtain ⟨B', hB', hBe⟩ := hy.1
      exact ⟨⟨A', B', hA', hB', hAe, hBe⟩,
        integral_mul_eq_of_corrected_halfSpace_versions Q (Renewal.forceCoord hd)
          (y (Renewal.forceCoord hd)) (l / lam) (sbxS5_radius_gap hl h0 h1 hsep)
          _ _ A' B' hA' hB' hAe hBe⟩
    · exact hfuture_local.mono fun _ hy => hy.2
    · exact weighted_slice_identity_assuming_path_laws_phys hd Q lam h0 h1 l δ hl hsep
        hδ0 hδ1 P K hK hP hendpoint hpast hfuture hslices hscope hD
        F hF hbF n hn H hH hbH Φ hΦ hbΦ
  · apply sbxS5_firstMarginal_of_sliceIdentity_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
      P K hK hscope hD Φ hΦ hbΦ
    intro n hn
    have hb1 {α : Type} : BoundedRealTest (fun _ : α => (1 : ℝ)) :=
      ⟨1, fun _ => by norm_num⟩
    simpa only [one_mul] using
      weighted_slice_identity_assuming_path_laws_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
        P K hK hP hendpoint hpast hfuture hslices hscope hD
        (fun _ => 1) measurable_const hb1 n hn (fun _ => 1) measurable_const hb1 Φ hΦ hbΦ

section StoppedFirstCycle
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hP : ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p)
include hl hsep hδ0 hδ1 hK
end StoppedFirstCycle
section StoppedFirstCycleLaw
variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hP : ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p)
    (hendpoint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
include hl hsep hδ0 hδ1 hK hP hendpoint hpast hfuture hslices hscope
include hD
omit hP hendpoint hpast hfuture hslices
include hP hendpoint hpast hfuture hslices
end StoppedFirstCycleLaw
end EinsteinFull.Blueprint.EndpointAverageTransport
