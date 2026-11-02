import EinsteinFull.Blueprint.G1.Proofs.S3PrebridgeK
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.Blueprint.G1.node_rt_u3A_global_u2D_geometry
import EinsteinFull.Frozen.RegenerationConditionedLaw
import EinsteinRelation.Regeneration.BoundedMeasurableKilledFutureVersion
import EinsteinRelation.Regeneration.AnnealedUniformEndpointRestart
import EinsteinRelation.Regeneration.FirstRegenerationEndpointFormula
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinRelation.Regeneration.EndpointGap
import EinsteinRelation.Regeneration.CorrectedHalfSpaceIndependence
import EinsteinRelation.Regeneration.EndpointBallVolume
import EinsteinRelation.Probability.LocalSigma

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion)

/-! # `rt:k-factor`, core `k`-cycle factorization

Disintegration of the `k`-th regeneration slice at the deterministic prebridge time,
and its factorization through the half-space locality inputs. -/

theorem bt_mul {α : Type*} {f g : α → ℝ} (hf : Regeneration.BoundedRealTest f)
    (hg : Regeneration.BoundedRealTest g) :
    Regeneration.BoundedRealTest (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨max C 0 * max D 0, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hC x).trans (le_max_left _ _))
    ((hD x).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)

/-- Paths staying in an open or closed set up to `mΔ` form a finite-history event. -/
theorem measurableSet_forall_mem_finiteHistory {d : ℕ} (Δ : ℝ≥0) (m : ℕ) (U : Set (Vec d))
    (hU : IsOpen U ∨ IsClosed U) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ m)
      {z | ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) * Δ → z.1 u ∈ U} := by
  have hglob : MeasurableSet {γ : Path d | ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) * Δ → γ u ∈ U} := by
    rcases hU with hU | hU
    · have h := ContinuousMap.isOpen_setOfPred_mapsTo (X := ℝ≥0) (Y := Vec d)
        (K := Set.Icc (0 : ℝ≥0) ((m : ℝ≥0) * Δ)) isCompact_Icc hU
      have hs : {γ : Path d | ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) * Δ → γ u ∈ U} =
          {f : C(ℝ≥0, Vec d) | Set.MapsTo f (Set.Icc 0 ((m : ℝ≥0) * Δ)) U} := by
        ext γ
        exact ⟨fun h u hu => h u hu.2, fun h u hu => h ⟨zero_le, hu⟩⟩
      rw [hs]
      exact h.measurableSet
    · have hs : {γ : Path d | ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) * Δ → γ u ∈ U} =
          ⋂ u ∈ Set.Iic ((m : ℝ≥0) * Δ), (fun γ : Path d => γ u) ⁻¹' U := by
        ext γ
        simp
      rw [hs]
      exact (isClosed_biInter fun u _ => hU.preimage (continuous_eval_const u)).measurableSet
  have hset : {z : CoupledSample d | ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) * Δ → z.1 u ∈ U} =
      Probability.stoppedHistorySample Δ m ⁻¹'
        (Prod.fst ⁻¹' {γ : Path d | ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) * Δ → γ u ∈ U}) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    refine forall_congr' fun u => imp_congr_right fun hu => ?_
    rw [Probability.stoppedHistorySample_path Δ m z u hu]
  rw [hset]
  exact Probability.measurable_stoppedHistorySample Δ m (measurable_fst hglob)

/-- Survival above `-R` through `mΔ`, in absolute coordinates. -/
abbrev survSet {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (m : ℕ) : Set (CoupledSample d) :=
  {z | ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) * Δ → -R < z.1 u i}

/-- The selected-prebridge event of `rt:k-factor`, with the optional survival check. -/
abbrev GsetK {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k n : ℕ) (b : Bool) :
    Set (CoupledSample d) :=
  tupleUnionS Δ lam R i k n ∩ {z | b = true → z ∈ survSet Δ R i (n - 1)}

/-- The indicator of the event `GsetK Δ lam R i k n b` on coupled samples. -/
noncomputable def Gk {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k n : ℕ) (b : Bool) :
    CoupledSample d → ℝ :=
  (GsetK Δ lam R i k n b).indicator (fun _ => (1 : ℝ))

theorem measurableSet_GsetK {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (i : Fin d) (k n : ℕ) (b : Bool) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ (n - 1))
      (GsetK Δ lam R i k n b) := by
  refine @MeasurableSet.inter _ (finiteHistorySigma Δ (n - 1)) _ _
    (measurableSet_tupleUnionS Δ hΔ lam R hR i k n) ?_
  by_cases hb : b = true
  · have h := measurableSet_forall_mem_finiteHistory (d := d) Δ (n - 1)
      {x : Vec d | -R < x i} (Or.inl (isOpen_lt continuous_const (continuous_apply i)))
    have e : {z : CoupledSample d | b = true → z ∈ survSet Δ R i (n - 1)} =
        {z | ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ → z.1 u ∈ {x : Vec d | -R < x i}} := by
      ext z
      simp [hb, survSet]
    rw [e]
    exact h
  · have e : {z : CoupledSample d | b = true → z ∈ survSet Δ R i (n - 1)} = Set.univ := by
      ext z
      simp [hb]
    rw [e]
    exact @MeasurableSet.univ _ (finiteHistorySigma Δ (n - 1))

theorem measurable_Gk {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (i : Fin d) (k n : ℕ) (b : Bool) :
    @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n - 1)) inferInstance
      (Gk Δ lam R i k n b) :=
  Measurable.indicator measurable_const (measurableSet_GsetK Δ hΔ lam R hR i k n b)

theorem boundedRealTest_Gk {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k n : ℕ) (b : Bool) :
    Regeneration.BoundedRealTest (Gk Δ lam R i k n b) :=
  ⟨1, fun z => by
    by_cases hz : z ∈ GsetK Δ lam R i k n b <;> simp [Gk, hz]⟩

theorem Gk_ne_zero_mem {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k n : ℕ) (b : Bool)
    (z : CoupledSample d) (hz : Gk Δ lam R i k n b z ≠ 0) :
    z ∈ tupleUnionS Δ lam R i k n := by
  by_cases h : z ∈ GsetK Δ lam R i k n b
  · exact h.1
  · exact absurd (by simp [Gk, h]) hz

/-! ## The `k`-slice disintegration -/

open scoped Classical in
theorem slice_k_disintegration {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hprebridge : node_rt_u3A_prebridge_u2D_kStmt) (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
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
  have hpre := (hprebridge d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).2
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
