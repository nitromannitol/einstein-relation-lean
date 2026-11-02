import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

private theorem endpoint_bounded_mul {α : Type*} (f g : α → ℝ)
    (hf : BoundedRealTest f) (hg : BoundedRealTest g) :
    BoundedRealTest (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨max C 0 * max D 0, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hC x).trans (le_max_left _ _))
    ((hD x).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)

/-- Deterministic restart, the successful endpoint law and spatial Fubini give
the literal endpoint disintegration, retaining the full finite-history test. -/
theorem node_app_u3A_factorization_u23_endpoint_u2D_disintegration_of_deps
    (hslices : node_app_u3A_factorization_u23_slicesStmt) :
    node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt := by
  classical
  intro d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hr hδ hδ₁ P K hK
  dsimp only
  intro F hF hbF n hn H hH hbH f hf hbf g hg hbg
  let R := l / lam
  let i := Renewal.forceCoord hd
  let Δ := Renewal.regenDelta lam
  let Φ : FutureState d i R → ℝ := fun r => f (r.1, r.2.1) * g r.2.2
  have hΦ : Measurable Φ :=
    (hf.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hg.comp measurable_snd.snd)
  have hbΦ : BoundedRealTest Φ := endpoint_bounded_mul _ _
    (by obtain ⟨C, hC⟩ := hbf; exact ⟨C, fun r => hC _⟩)
    (by obtain ⟨C, hC⟩ := hbg; exact ⟨C, fun r => hC _⟩)
  have hFm : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  obtain ⟨C, _, B, hB, hbB, _hBo, hBp⟩ :=
    exists_globally_bounded_measurable_killed_future_version Q.measure K hK.1 R i Φ hΦ hbΦ
  let W : Vec d × FieldPair d → ℝ := fun p => F p.2 * B p
  have hW : Measurable W := (hFm.comp measurable_snd).mul hB
  have hbW : BoundedRealTest W := endpoint_bounded_mul _ _
    (by obtain ⟨D, hD⟩ := hbF; exact ⟨D, fun p => hD _⟩) ⟨C, hbB⟩
  let Ψ : (Vec d × FieldPair d) × CoupledSample d → ℝ :=
    fun p => F p.1.2 * killedFutureTest R i Φ p
  have hΨ : Measurable Ψ := (hFm.comp measurable_fst.snd).mul
    (measurable_killedFutureTest R i Φ hΦ)
  have hbΨ : BoundedRealTest Ψ := endpoint_bounded_mul _ _
    (by obtain ⟨D, hD⟩ := hbF; exact ⟨D, fun p => hD _⟩)
    (boundedRealTest_killedFutureTest R i Φ hbΦ)
  have hWp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      W p = ∫ z, Ψ (p, z) ∂K p := by
    filter_upwards [hBp] with p hp
    dsimp only [W, Ψ]
    rw [integral_const_mul, hp]
    rfl
  let G := (forcedBitTrialEvent Δ lam R i (n - 1)).indicator H
  have hG : Measurable[finiteHistorySigma Δ (n - 1)] G :=
    hH.indicator ((hslices d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hr hδ hδ₁ P K hK n hn).1)
  have hbG : BoundedRealTest G := by
    obtain ⟨D, hD⟩ := hbH
    refine ⟨max D 0, fun z => ?_⟩
    by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i (n - 1)
    · simpa only [G, Set.indicator_of_mem hz] using (hD z).trans (le_max_left D 0)
    · simpa only [G, Set.indicator_of_notMem hz, abs_zero] using le_max_right D 0
  have he := integral_annealed_future_eq_uniformEndpointAverage hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1 Δ hΔ δ R i hK.2.2.2.2.1 hK.2.2.2.2.2.2.1
    (n - 1) G hG hbG Ψ hΨ hbΨ W hW hbW hWp
  have hfu := integral_annealed_endpointAverage_fubini Q.measure K hK.1 Δ (n - 1) i R hR
    G (hG.mono (Probability.finiteHistorySigma_le Δ (n - 1)) le_rfl) hbG W hW hbW
  rw [integral_const_mul, hfu] at he
  have hn' : n - 1 + 1 = n := by omega
  have htime (z : CoupledSample d) : regenerationTime hd lam l 1 z =
      firstRegenerationTime Δ lam R z i := regenerationTime_one _ _ _ _ _
  have hrecord : regenerationRecord hd lam l 1 = iteratedRecord Δ lam R i 1 := rfl
  rw [hn'] at he
  have hs : MeasurableSet {q : FieldPair d × CoupledSample d |
      regenerationTime hd lam l 1 q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} := by
    simp only [htime]
    exact ((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd)
      (measurableSet_singleton _)
  change (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
    F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q)
      ∂annealedCoupledLaw Q.measure K) = _
  rw [← integral_indicator hs]
  have hind (q : FieldPair d × CoupledSample d) :
      ({q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}.indicator
        (fun q => F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q))) q =
      G q.2 * (if q.2.2 (n - 1) = true then (1 : ℝ) else 0) *
        Ψ ((q.2.1 (((n : ℝ≥0) * Δ)), q.1), sampleTimeShift Δ q.2 ((n : ℝ≥0) * Δ)) := by
    have hid := firstRegeneration_slice_integrand Δ hΔ lam R i (n - 1) H Φ q
    rw [hn'] at hid
    simp only [htime, hrecord]
    rw [show (fun q : FieldPair d × CoupledSample d => F q.1 * H q.2 *
        Φ (iteratedRecord Δ lam R i 1 q)) =
        (fun q => F q.1 * (H q.2 * Φ (iteratedRecord Δ lam R i 1 q))) by
          funext q; ring, Set.indicator_mul_right, hid]
    dsimp only [Ψ]
    ring
  simp_rw [hind]
  rw [he]
  simp only [div_eq_mul_inv, mul_assoc]
  congr 1
  congr 1
  apply integral_congr_ae
  have hp := Measure.ae_ae_of_ae_prod hBp
  filter_upwards [hp] with y hy
  apply integral_congr_ae
  filter_upwards [hy] with ω hω
  change firstSlicePastIntegral Δ lam R i (n - 1) K H (y, ω) * (F ω * B (y, ω)) =
    F ω * (firstSlicePastIntegral Δ lam R i (n - 1) K H (y, ω) *
      ∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω))
  change B (y, ω) = ∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω) at hω
  rw [hω]
  ring

end EinsteinFull.Blueprint
