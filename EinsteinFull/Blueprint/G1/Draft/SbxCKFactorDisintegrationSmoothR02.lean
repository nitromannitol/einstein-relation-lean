import EinsteinFull.Blueprint.G1.Proofs.S3KFactorCore
import EinsteinFull.Frozen.SmoothEnvironment

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion)

/-! Smooth-law prebridge input and its conditional k-slice disintegration. -/

set_option linter.unusedVariables false in
def prebridgeKSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (_hl : 0 < l) (_hsep : D.dependenceRange < 2 * l) (_hδ₀ : 0 < δ) (_hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let tupleEvent := fun (k n : ℕ) (a : Fin (k + 1) → ℕ) =>
    {z : Regeneration.CoupledSample d |
      a 0 = 0 ∧ a (Fin.last k) = n ∧
      (∀ j : Fin k, a j.castSucc + 2 ≤ a j.succ) ∧
      (∀ j : Fin k,
        Regeneration.sampleTimeShift Δ z ((a j.castSucc : ℝ≥0) * Δ) ∈
          Regeneration.forcedBitTrialEvent Δ lam R i (a j.succ - a j.castSucc - 1)) ∧
      (∀ j : Fin k, j.val + 1 < k → z.2 (a j.succ - 1) = true) ∧
      (∀ j : Fin k, j.val + 1 < k → ∀ u : ℝ≥0,
        (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
        z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i)}
  let Γ := fun k n => ⋃ a : Fin (k + 1) → Fin (n + 1),
    tupleEvent k n (fun j => (a j).val)
  ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n →
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (n - 1)) (Γ k n) ∧
    (∀ᵐ ωz ∂Regeneration.annealedCoupledLaw Q.measure K,
      (regenerationTime hd lam l k ωz.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔
        ωz.2 ∈ Γ k n ∧ ωz.2.2 (n - 1) = true ∧
          Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift ωz.2.1 ((n : ℝ≥0) * Δ)) i) ∧
      (ωz.2 ∈ Γ k n → ωz.2.2 (n - 1) = true →
        Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift ωz.2.1 ((n : ℝ≥0) * Δ)) i →
        ∃! a : Fin (k + 1) → Fin (n + 1),
          ωz.2 ∈ tupleEvent k n (fun j => (a j).val) ∧
          ∀ j : Fin (k + 1), regenerationTime hd lam l j.val ωz.2 =
            ((((a j).val : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)))

open scoped Classical in
theorem slice_k_disintegration_smooth {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : D.dependenceRange < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hprebridge : prebridgeKSmoothStmt) (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (G : CoupledSample d → ℝ)
    (hG : @Measurable (CoupledSample d) ℝ
      (finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (n - 1)) inferInstance G)
    (hbG : Regeneration.BoundedRealTest G)
    (hGΓ : ∀ z, G z ≠ 0 → z ∈ tupleUnionS (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) k n)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
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
            ((y, ω), z) ∂K (y, ω)) ∂Q.measure := by
  classical
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  obtain ⟨C, _, B, hB, hbB, _hBo, hBp⟩ :=
    Regeneration.exists_globally_bounded_measurable_killed_future_version Q.measure K hK.1
      (l / lam) (Regeneration.Renewal.forceCoord hd) Φ hΦ hbΦ
  let W : Vec d × FieldPair d → ℝ := fun p => F p.2 * B p
  have hW : Measurable W := (hF.comp measurable_snd).mul hB
  have hbW : Regeneration.BoundedRealTest W :=
    bt_mul (by obtain ⟨D, hD⟩ := hbF; exact ⟨D, fun p => hD _⟩) ⟨C, hbB⟩
  let Ψ : (Vec d × FieldPair d) × CoupledSample d → ℝ := fun p =>
    F p.1.2 * Regeneration.killedFutureTest (l / lam) (Regeneration.Renewal.forceCoord hd) Φ p
  have hΨ : Measurable Ψ := (hF.comp measurable_fst.snd).mul
    (Regeneration.measurable_killedFutureTest _ _ Φ hΦ)
  have hbΨ : Regeneration.BoundedRealTest Ψ :=
    bt_mul (by obtain ⟨D, hD⟩ := hbF; exact ⟨D, fun p => hD _⟩)
      (Regeneration.boundedRealTest_killedFutureTest _ _ Φ hbΦ)
  have hWp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      W p = ∫ z, Ψ (p, z) ∂K p := by
    filter_upwards [hBp] with p hp
    dsimp only [W, Ψ]
    rw [integral_const_mul, hp]
    rfl
  have hGg : Measurable G :=
    hG.mono (Probability.finiteHistorySigma_le (d := d) (Regeneration.Renewal.regenDelta lam)
      (n - 1)) le_rfl
  have he := Regeneration.integral_annealed_future_eq_uniformEndpointAverage hd Q lam h₀.le h₁
    P K hK.1 hK.2.1 hK.2.2.1 (Regeneration.Renewal.regenDelta lam) hΔ δ (l / lam)
    (Regeneration.Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.1 (n - 1) G hG hbG
    Ψ hΨ hbΨ W hW hbW hWp
  have hfu := Regeneration.integral_annealed_endpointAverage_fubini Q.measure K hK.1
    (Regeneration.Renewal.regenDelta lam) (n - 1) (Regeneration.Renewal.forceCoord hd) (l / lam)
    hR G hGg hbG W hW hbW
  rw [integral_const_mul, hfu] at he
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at he
  have hs : MeasurableSet {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} :=
    measurableSet_eq_fun
      ((Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
        (l / lam) (Regeneration.Renewal.forceCoord hd) k).comp measurable_snd)
      measurable_const
  rw [← integral_indicator hs]
  have hpre := (hprebridge d hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).2
  have hint : (∫ q, ({q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}.indicator
        (fun q => F q.1 * G q.2 * Φ (regenerationRecord hd lam l k q))) q
        ∂Regeneration.annealedCoupledLaw Q.measure K) =
      ∫ q, G q.2 * (if q.2.2 (n - 1) = true then (1 : ℝ) else 0) *
        Ψ ((q.2.1 (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam)), q.1),
          sampleTimeShift (Regeneration.Renewal.regenDelta lam) q.2
            ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        ∂Regeneration.annealedCoupledLaw Q.measure K := by
    apply integral_congr_ae
    filter_upwards [hpre] with q hq
    have hrec : regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) →
        regenerationRecord hd lam l k q = Regeneration.futureRecord
          (Regeneration.Renewal.regenDelta lam) (l / lam) q.1 q.2
          (Regeneration.Renewal.forceCoord hd)
          ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam) := by
      intro hτ
      have hτ' : Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam
          (l / lam) q.2 (Regeneration.Renewal.forceCoord hd) k =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := hτ
      unfold regenerationRecord Regeneration.Renewal.cycleRecord
      rw [hτ', ENNReal.toNNReal_coe]
    by_cases ht : regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)
    · obtain ⟨_, hcoin, hNB⟩ := hq.1.mp ht
      rw [Set.indicator_of_mem (show q ∈ {q : FieldPair d × CoupledSample d |
        regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} from ht),
        hrec ht]
      dsimp only [Ψ]
      rw [Regeneration.killedFutureTest_sampleTimeShift, if_pos hNB]
      simp only [hcoin, ↓reduceIte, mul_one]
      ring
    · rw [Set.indicator_of_notMem (show q ∉ {q : FieldPair d × CoupledSample d |
        regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} from ht)]
      by_cases hG0 : G q.2 = 0
      · simp [hG0]
      · have hΓq := hGΓ _ hG0
        by_cases hcoin : q.2.2 (n - 1) = true
        · have hNB : ¬ NoBacktracking (l / lam) (pathTimeShift q.2.1
              ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
              (Regeneration.Renewal.forceCoord hd) :=
            fun h => ht (hq.1.mpr ⟨hΓq, hcoin, h⟩)
          dsimp only [Ψ]
          rw [Regeneration.killedFutureTest_sampleTimeShift, if_neg hNB]
          simp
        · simp [hcoin]
  rw [hint, he, div_eq_mul_inv δ, mul_assoc δ]
  congr 1
  congr 1
  apply integral_congr_ae
  have hp := Measure.ae_ae_of_ae_prod hBp
  filter_upwards [hp] with y hy
  apply integral_congr_ae
  filter_upwards [hy] with ω hω
  change (∫ z, G z * (if y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd)
      (l / lam) (z.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
      then (1 : ℝ) else 0) ∂K (0, ω)) * (F ω * B (y, ω)) =
    F ω * (∫ z, G z * (if y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd)
      (l / lam) (z.1 (((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
      then (1 : ℝ) else 0) ∂K (0, ω)) *
      ∫ z, Regeneration.killedFutureTest (l / lam) (Regeneration.Renewal.forceCoord hd) Φ
        ((y, ω), z) ∂K (y, ω)
  change B (y, ω) = ∫ z, Regeneration.killedFutureTest (l / lam)
    (Regeneration.Renewal.forceCoord hd) Φ ((y, ω), z) ∂K (y, ω) at hω
  rw [hω]
  ring

end EinsteinFull.Blueprint
