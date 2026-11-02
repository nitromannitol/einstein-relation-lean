import EinsteinFull.Blueprint.G1.Proofs.S3KFactorLocal
import EinsteinRelation.Regeneration.KilledFutureConditionalMean

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion)

/-! # `rt:k-factor`: the product identity at the `k`-th slice -/

open scoped Classical in
theorem slice_k_factor_core {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (hprebridge : node_rt_u3A_prebridge_u2D_kStmt)
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
  rw [slice_k_disintegration hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hprebridge k n hk hn
    (Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam) (Regeneration.Renewal.forceCoord hd)
      k n b)
    (measurable_Gk _ hΔ lam _ hR _ k n b) (boundedRealTest_Gk _ lam _ _ k n b)
    (fun z hz => Gk_ne_zero_mem _ _ _ _ _ _ _ z hz) F hFg hbF Φ hΦ hbΦ]
  have hy := factor_ae_y hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast hindep
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

/-! ## The no-return event on a slice -/

theorem center_mem_endpointBall {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R) (x : Vec d) :
    x + (9 * R) • unitVector i ∈ Regeneration.endpointBall i R x := by
  show euclideanNorm (x + (9 * R) • unitVector i - (x + (9 * R) • unitVector i)) < R
  rw [sub_self]
  simpa [euclideanNorm, euclideanSq, dot] using hR

theorem noBacktracking_iff_surv {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (hR : 0 < R) (i : Fin d)
    (z : CoupledSample d) (n : ℕ) (hz0 : z.1 0 i = 0)
    (hpos : R ≤ z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ) i)
    (hgain : z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ) i + 8 * R ≤ z.1 ((n : ℝ≥0) * Δ) i)
    (hsupp : ∀ t : ℝ≥0, ((n - 1 : ℕ) : ℝ≥0) * Δ ≤ t → t ≤ (n : ℝ≥0) * Δ →
      z.1 t ∈ couplingRegion i R (z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ)))
    (hNB : NoBacktracking R (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) i) :
    NoBacktracking R z.1 i ↔
      ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ → -R < z.1 u i := by
  rw [Regeneration.noBacktracking_iff_forall]
  constructor
  · intro h u _
    have := h u
    linarith
  · intro h t
    by_cases ht1 : t ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ
    · have := h t ht1
      linarith
    · by_cases ht2 : t ≤ (n : ℝ≥0) * Δ
      · have hreg := hsupp t (le_of_not_ge ht1) ht2
        have := (Regeneration.couplingRegion_coordinate_bounds i R _ _ hreg).1
        linarith
      · have hnb := (Regeneration.noBacktracking_iff_forall R _ i).mp hNB
          (t - (n : ℝ≥0) * Δ)
        change -R < z.1 ((n : ℝ≥0) * Δ + (t - (n : ℝ≥0) * Δ)) i -
          z.1 ((n : ℝ≥0) * Δ + 0) i at hnb
        rw [add_tsub_cancel_of_le (lt_of_not_ge ht2).le, add_zero] at hnb
        linarith

theorem ae_noReturn_iff_surv {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hprebridge : node_rt_u3A_prebridge_u2D_kStmt) (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
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
  have hg := hgeom d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  have hpre := (hprebridge d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).2
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

end EinsteinFull.Blueprint
