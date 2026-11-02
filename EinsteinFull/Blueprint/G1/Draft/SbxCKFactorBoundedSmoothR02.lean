import EinsteinFull.Blueprint.G1.Proofs.S3KFactorBounded
import EinsteinFull.Blueprint.G1.Draft.SbxCKFactorLocalSmoothR02
import EinsteinFull.Blueprint.G1.Proofs.W2Queue0440

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion)

/-! Conditional smooth-law k-slice product identities. -/

open scoped Classical in
set_option linter.unusedVariables false in
def sliceDisintegrationInputStmt : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : D.dependenceRange < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (G : CoupledSample d → ℝ)
    (hG : @Measurable (CoupledSample d) ℝ
      (finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (n - 1)) inferInstance G)
    (hbG : Regeneration.BoundedRealTest G)
    (hGΓ : ∀ z, G z ≠ 0 → z ∈ tupleUnionS (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) k n)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ),
    (∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * G q.2 * Φ (regenerationRecord hd lam l k q)
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      δ / (volume (Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
        (0 : Vec d))).toReal *
        ∫ y, ∫ ω, F ω * (∫ z, G z * (if y ∈ Regeneration.endpointBall
          (Regeneration.Renewal.forceCoord hd) (l / lam)
          (z.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) then (1 : ℝ) else 0)
          ∂K (0, ω)) *
          (∫ z, Regeneration.killedFutureTest (l / lam) (Regeneration.Renewal.forceCoord hd) Φ
            ((y, ω), z) ∂K (y, ω)) ∂Q.measure

open scoped Classical in
theorem slice_k_factor_core_smooth {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : D.dependenceRange < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : SbxCFactorizationR01.pastKernelSmoothStmt)
    (hindep : SbxCFactorizationR01.independenceSmoothStmt)
    (hdis : sliceDisintegrationInputStmt)
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) (b : Bool)
    (F : FieldPair d → ℝ)
    (hFloc : Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
      (10 * (k : ℝ) - 4) * (l / lam)}] F)
    (hbF : Regeneration.BoundedRealTest F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    (∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n b q.2 *
        Φ (regenerationRecord hd lam l k q) ∂Regeneration.annealedCoupledLaw Q.measure K) =
      (∫ q in regenerationNoReturn hd (l / lam),
        Φ (regenerationRecord hd lam l 0 q) ∂Regeneration.annealedCoupledLaw Q.measure K) *
      (δ / (volume (Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
        (0 : Vec d))).toReal *
        ∫ y, ∫ ω, F ω * AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n b y ω ∂Q.measure) := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  have hFg : Measurable F := hFloc.mono (Probability.localSigma_le_borel _) le_rfl
  rw [hdis hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn
    (Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam) (Regeneration.Renewal.forceCoord hd)
      k n b)
    (measurable_Gk _ hΔ lam _ hR _ k n b) (boundedRealTest_Gk _ lam _ _ k n b)
    (fun z hz => Gk_ne_zero_mem _ _ _ _ _ _ _ z hz) F hFg hbF Φ hΦ hbΦ]
  have hy := factor_ae_y_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast hindep
    k n hk hn b F hFloc Φ hΦ hbΦ
  have hint : (∫ y, ∫ ω, F ω * (∫ z, Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n b z * (if y ∈ Regeneration.endpointBall
          (Regeneration.Renewal.forceCoord hd) (l / lam)
          (z.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) then (1 : ℝ) else 0)
          ∂K (0, ω)) *
        (∫ z, Regeneration.killedFutureTest (l / lam) (Regeneration.Renewal.forceCoord hd) Φ
          ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
      (∫ y, ∫ ω, F ω * AyK K (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n b y ω ∂Q.measure) *
        ∫ q in regenerationNoReturn hd (l / lam),
          Φ (regenerationRecord hd lam l 0 q) ∂Regeneration.annealedCoupledLaw Q.measure K := by
    rw [← integral_mul_const]
    exact integral_congr_ae hy
  rw [hint]
  ring


/-! The bounded consequences use the proved slice characterization. -/

theorem ae_noReturn_iff_surv_smooth {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : D.dependenceRange < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
      regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd (l / lam) ↔
        q.2 ∈ survSet (Regeneration.Renewal.regenDelta lam) (l / lam)
          (Regeneration.Renewal.forceCoord hd) (n - 1)) := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  have hn1 : 1 ≤ n := by omega
  let M : Set (FieldPair d × CoupledSample d) := {q |
    q.2.1 0 (Regeneration.Renewal.forceCoord hd) = 0 →
    l / lam ≤ q.2.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)
      (Regeneration.Renewal.forceCoord hd) →
    q.2.2 (n - 1) = true →
    NoBacktracking (l / lam) (pathTimeShift q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
      (Regeneration.Renewal.forceCoord hd) →
    (NoBacktracking (l / lam) q.2.1 (Regeneration.Renewal.forceCoord hd) ↔
      q.2 ∈ survSet (Regeneration.Renewal.regenDelta lam) (l / lam)
        (Regeneration.Renewal.forceCoord hd) (n - 1))}
  have hev (u : ℝ≥0) : Measurable (fun q : FieldPair d × CoupledSample d =>
      q.2.1 u (Regeneration.Renewal.forceCoord hd)) :=
    (measurable_pi_apply (Regeneration.Renewal.forceCoord hd)).comp
      ((continuous_eval_const u).measurable.comp measurable_snd.fst)
  have hs1 : MeasurableSet {q : FieldPair d × CoupledSample d |
      q.2.1 0 (Regeneration.Renewal.forceCoord hd) = 0} :=
    measurableSet_eq_fun (hev 0) measurable_const
  have hs2 : MeasurableSet {q : FieldPair d × CoupledSample d |
      l / lam ≤ q.2.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)
        (Regeneration.Renewal.forceCoord hd)} :=
    measurableSet_le measurable_const (hev _)
  have hs3 : MeasurableSet {q : FieldPair d × CoupledSample d | q.2.2 (n - 1) = true} :=
    measurableSet_eq_fun ((measurable_pi_apply (n - 1)).comp measurable_snd.snd) measurable_const
  have hshift : Measurable (fun q : FieldPair d × CoupledSample d =>
      pathTimeShift q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) :=
    Probability.continuous_path_time_shift.measurable.comp
      (measurable_const.prodMk measurable_snd.fst)
  have hs4 : MeasurableSet {q : FieldPair d × CoupledSample d |
      NoBacktracking (l / lam)
        (pathTimeShift q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        (Regeneration.Renewal.forceCoord hd)} :=
    (Regeneration.measurableSet_NoBacktracking (l / lam) (Regeneration.Renewal.forceCoord hd)).preimage
      hshift
  have hs5 : MeasurableSet {q : FieldPair d × CoupledSample d |
      NoBacktracking (l / lam) q.2.1 (Regeneration.Renewal.forceCoord hd)} :=
    (Regeneration.measurableSet_NoBacktracking (l / lam) (Regeneration.Renewal.forceCoord hd)).preimage
      measurable_snd.fst
  have hs6 : MeasurableSet {q : FieldPair d × CoupledSample d |
      q.2 ∈ survSet (Regeneration.Renewal.regenDelta lam) (l / lam)
        (Regeneration.Renewal.forceCoord hd) (n - 1)} :=
    ((Probability.finiteHistorySigma_le (d := d) (Regeneration.Renewal.regenDelta lam) (n - 1))
      _ (measurableSet_forall_mem_finiteHistory (d := d) (Regeneration.Renewal.regenDelta lam)
        (n - 1) {x : Vec d | -(l / lam) < x (Regeneration.Renewal.forceCoord hd)}
        (Or.inl (isOpen_lt continuous_const (continuous_apply _))))).preimage measurable_snd
  have hM : MeasurableSet M :=
    MeasurableSet.imp hs1 (MeasurableSet.imp hs2 (MeasurableSet.imp hs3
      (MeasurableSet.imp hs4 (MeasurableSet.iff hs5 hs6))))
  have hae : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, q ∈ M := by
    refine ae_mem_of_facts hd Q lam h₀ h₁ l δ P K hK M hM ?_
    intro z hgain hsupp ω hz0 hpos hcoin hNB
    have hgn := hgain (n - 1) hcoin
    rw [Nat.sub_add_cancel hn1] at hgn
    have hsn := hsupp (n - 1) hcoin
    rw [Nat.sub_add_cancel hn1] at hsn
    exact noBacktracking_iff_surv (Regeneration.Renewal.regenDelta lam) (l / lam) hR _ z n hz0 hpos
      hgn hsn hNB
  have hstart := Regeneration.ae_origin_start_of_isGMPReducedKernel hd Q lam h₀.le h₁ P K hK.1 hK.2.1 hK.2.2.1
  have hg := hgeom d hd D.ellipticity D.dependenceRange Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  have hpre := (node_rt_u3A_prebridge_u2D_k_of_deps
    node_app_u3A_factorization_u23_slices_of_deps d hd D.ellipticity D.dependenceRange Q
    lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).2
  filter_upwards [hae, hstart, hg, hpre] with q hqM hq0 hqg hqp hτ
  obtain ⟨hΓ, hcoin, hNB⟩ := (hqp.1.mp hτ)
  have hpos : l / lam ≤ q.2.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)
      (Regeneration.Renewal.forceCoord hd) := by
    have hc := center_mem_endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam) hR
      (q.2.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
    have h10 := (hqg k n hk hn hΓ).2 _ hc |>.1
    have hcoord : (q.2.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam) +
        (9 * (l / lam)) • unitVector (Regeneration.Renewal.forceCoord hd))
        (Regeneration.Renewal.forceCoord hd) =
        q.2.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)
          (Regeneration.Renewal.forceCoord hd) + 9 * (l / lam) := by
      simp [unitVector]
    rw [hcoord] at h10
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hk1)]
  have h0 : q.2.1 0 (Regeneration.Renewal.forceCoord hd) = 0 := by
    rw [hq0]
    rfl
  exact hqM h0 hpos hcoin hNB


open scoped Classical in
theorem bounded_factor_mu_smooth {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : D.dependenceRange < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : SbxCFactorizationR01.pastKernelSmoothStmt)
    (hindep : SbxCFactorizationR01.independenceSmoothStmt)
    (hdis : sliceDisintegrationInputStmt)
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (F : FieldPair d → ℝ)
    (hFloc : Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
      (10 * (k : ℝ) - 4) * (l / lam)}] F)
    (hbF : Regeneration.BoundedRealTest F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    (∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * Φ (regenerationRecord hd lam l k q) ∂Regeneration.annealedCoupledLaw Q.measure K) =
      (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
      ∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 ∂Regeneration.annealedCoupledLaw Q.measure K := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  haveI hμprob : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let N := regenerationNoReturn hd (l / lam)
  let slice : Set (FieldPair d × CoupledSample d) := {q | regenerationTime hd lam l k q.2 =
    (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs : MeasurableSet slice :=
    measurableSet_eq_fun
      ((Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
        (l / lam) (Regeneration.Renewal.forceCoord hd) k).comp measurable_snd)
      measurable_const
  let Φ1 : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ :=
    fun _ => 1
  have hcore := slice_k_factor_core_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast
    hindep hdis k n hk hn false F hFloc hbF Φ hΦ hbΦ
  have hcore1 := slice_k_factor_core_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast
    hindep hdis k n hk hn false F hFloc hbF Φ1 measurable_const ⟨1, fun _ => by norm_num⟩
  have hpre := (node_rt_u3A_prebridge_u2D_k_of_deps
    node_app_u3A_factorization_u23_slices_of_deps d hd D.ellipticity D.dependenceRange Q
    lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).2
  have hGk : ∀ᵐ q ∂μ, q ∈ slice →
      Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n false q.2 = 1 := by
    filter_upwards [hpre] with q hq hmem
    have hΓ := (hq.1.mp hmem).1
    have hmemG : q.2 ∈ GsetK (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n false :=
      ⟨hΓ, fun h => absurd h (by simp)⟩
    simp only [Gk, Set.indicator_of_mem hmemG]
  have e1 : (∫ q in slice, F q.1 * Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) k n false q.2 *
      Φ (regenerationRecord hd lam l k q) ∂μ) =
      ∫ q in slice, F q.1 * Φ (regenerationRecord hd lam l k q) ∂μ := by
    apply setIntegral_congr_ae hs
    filter_upwards [hGk] with q hq hmem
    rw [hq hmem, mul_one]
  have e2 : (∫ q in slice, F q.1 * Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) k n false q.2 *
      Φ1 (regenerationRecord hd lam l k q) ∂μ) = ∫ q in slice, F q.1 ∂μ := by
    apply setIntegral_congr_ae hs
    filter_upwards [hGk] with q hq hmem
    simp only [Φ1, hq hmem, mul_one]
  have hc1 : (∫ q in N, Φ1 (regenerationRecord hd lam l 0 q) ∂μ) = (μ N).toReal := by
    simp [Φ1, measureReal_def]
  have hμD : 0 < (μ N).toReal := ENNReal.toReal_pos hD (measure_ne_top _ _)
  rw [e1] at hcore
  rw [e2, hc1] at hcore1
  change (∫ q in slice, F q.1 * Φ (regenerationRecord hd lam l k q) ∂μ) =
    (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ProbabilityTheory.cond μ N) *
      ∫ q in slice, F q.1 ∂μ
  rw [integral_cond_eq, hcore, hcore1]
  have := hμD.ne'
  field_simp
  try ring

open scoped Classical in
theorem bounded_factor_nu_smooth {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : D.dependenceRange < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : SbxCFactorizationR01.pastKernelSmoothStmt)
    (hindep : SbxCFactorizationR01.independenceSmoothStmt)
    (hdis : sliceDisintegrationInputStmt)
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (F : FieldPair d → ℝ)
    (hFloc : Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
      (10 * (k : ℝ) - 4) * (l / lam)}] F)
    (hbF : Regeneration.BoundedRealTest F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    (∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * Φ (regenerationRecord hd lam l k q) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) =
      (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
      ∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  haveI hμprob : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let N := regenerationNoReturn hd (l / lam)
  have hDm : MeasurableSet N :=
    (Regeneration.measurableSet_NoBacktracking (l / lam) (Regeneration.Renewal.forceCoord hd)).preimage
      measurable_snd.fst
  let slice : Set (FieldPair d × CoupledSample d) := {q | regenerationTime hd lam l k q.2 =
    (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs : MeasurableSet slice :=
    measurableSet_eq_fun
      ((Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
        (l / lam) (Regeneration.Renewal.forceCoord hd) k).comp measurable_snd)
      measurable_const
  let Φ1 : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ :=
    fun _ => 1
  have hcore := slice_k_factor_core_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast
    hindep hdis k n hk hn true F hFloc hbF Φ hΦ hbΦ
  have hcore1 := slice_k_factor_core_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast
    hindep hdis k n hk hn true F hFloc hbF Φ1 measurable_const ⟨1, fun _ => by norm_num⟩
  have hpre := (node_rt_u3A_prebridge_u2D_k_of_deps
    node_app_u3A_factorization_u23_slices_of_deps d hd D.ellipticity D.dependenceRange Q
    lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).2
  have hnr := ae_noReturn_iff_surv_smooth hd D Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hgeom
    k n hk hn
  have hind : ∀ Φ' : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd)
      (l / lam) → ℝ, (∫ q in slice ∩ N, F q.1 * Φ' (regenerationRecord hd lam l k q) ∂μ) =
      ∫ q in slice, F q.1 * Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n true q.2 *
        Φ' (regenerationRecord hd lam l k q) ∂μ := by
    intro Φ'
    rw [← setIntegral_indicator hDm]
    apply setIntegral_congr_ae hs
    filter_upwards [hpre, hnr] with q hq hq2 hmem
    have hΓ := (hq.1.mp hmem).1
    by_cases hqD : q ∈ N
    · have hsurv := (hq2 hmem).mp hqD
      have hmemG : q.2 ∈ GsetK (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n true := ⟨hΓ, fun _ => hsurv⟩
      rw [Set.indicator_of_mem hqD]
      simp only [Gk, Set.indicator_of_mem hmemG, mul_one]
    · have hnotG : q.2 ∉ GsetK (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n true :=
        fun h => hqD ((hq2 hmem).mpr (h.2 rfl))
      rw [Set.indicator_of_notMem hqD]
      simp only [Gk, Set.indicator_of_notMem hnotG, mul_zero, zero_mul]
  have hind1 : (∫ q in slice ∩ N, F q.1 ∂μ) = ∫ q in slice, F q.1 * Gk
      (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n true q.2 * Φ1 (regenerationRecord hd lam l k q) ∂μ := by
    rw [← hind Φ1]
    simp [Φ1]
  have hc1 : (∫ q in N, Φ1 (regenerationRecord hd lam l 0 q) ∂μ) = (μ N).toReal := by
    simp [Φ1, measureReal_def]
  have hμD : 0 < (μ N).toReal := ENNReal.toReal_pos hD (measure_ne_top _ _)
  rw [← hind] at hcore
  rw [← hind1, hc1] at hcore1
  change (∫ q in slice, F q.1 * Φ (regenerationRecord hd lam l k q)
      ∂ProbabilityTheory.cond μ N) =
    (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ProbabilityTheory.cond μ N) *
      ∫ q in slice, F q.1 ∂ProbabilityTheory.cond μ N
  rw [setIntegral_cond_eq μ N slice hs, setIntegral_cond_eq μ N slice hs, integral_cond_eq,
    hcore, hcore1]
  have := hμD.ne'
  field_simp
  try ring

end EinsteinFull.Blueprint
