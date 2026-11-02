import EinsteinFull.Blueprint.G1.Proofs.S3KFactorBounded
import EinsteinFull.Blueprint.G1.node_rt_u3A_k_u2D_factor
import EinsteinRelation.Regeneration.CycleRecordMeasurability

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion)

/-! # `rt:k-factor` -/

theorem ite_aux (P1 P2 P3 : Prop) [Decidable (P1 ∧ P2 ∧ P3)] [Decidable (P1 ∧ P3)]
    [Decidable P2] :
    (if P1 ∧ P2 ∧ P3 then (1 : ℝ) else 0) = (if P1 ∧ P3 then (1 : ℝ) else 0) *
      (if P2 then (1 : ℝ) else 0) := by
  by_cases h1 : P1 <;> by_cases h2 : P2 <;> by_cases h3 : P3 <;> simp [h1, h2, h3]

theorem node_rt_u3A_k_u2D_factor_of_deps
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (hprebridge : node_rt_u3A_prebridge_u2D_kStmt) :
    node_rt_u3A_k_u2D_factorStmt := by
  classical
  intro d hd Λ₀ r₀ l δ hl hsep hδ₀ hδ₁
  refine ⟨3 + 1 / l, by positivity, ?_⟩
  intro Q lam h₀ h₁ P K hK
  dsimp only
  intro hD A hA
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = max 1 ⌈(A / l + 4) / 10⌉₊ := ⟨_, rfl⟩
  rw [← hkdef]
  have hk1 : 1 ≤ k := by rw [hkdef]; exact le_max_left _ _
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  have hA0 : 0 ≤ A := by linarith
  have hAl0 : 0 ≤ A / l := div_nonneg hA0 hl.le
  refine ⟨?_, ?_, ?_⟩
  · -- size of the cycle count
    have hx0 : 0 ≤ (A / l + 4) / 10 := by linarith
    have hceil : (⌈(A / l + 4) / 10⌉₊ : ℝ) < (A / l + 4) / 10 + 1 := Nat.ceil_lt_add_one hx0
    have hk' : (k : ℝ) ≤ (A / l + 4) / 10 + 1 := by
      rw [hkdef, Nat.cast_max]
      exact max_le (by simp only [Nat.cast_one]; linarith) hceil.le
    have hu : 0 ≤ 1 / l := by positivity
    have hAl : A / l = A * (1 / l) := by ring
    nlinarith [mul_nonneg hA0 hu]
  · -- local versions of the past kernel
    intro n hn y b
    obtain ⟨A', hA', hAe⟩ := AyK_local hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hgeom hpast k n
      hk1 hn b y
    refine ⟨A', hA', ?_⟩
    refine Filter.EventuallyEq.trans ?_ hAe
    refine Filter.Eventually.of_forall fun ω => ?_
    unfold AyK
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun z => ?_
    have hGk : Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n b z =
        if z ∈ GsetK (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n b then 1 else 0 := by
      simp only [Gk, Set.indicator_apply]
    have hmemG : z ∈ GsetK (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n b ↔
        (z ∈ tupleUnionS (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n ∧
        (b = true → ∀ u : ℝ≥0,
          u ≤ ((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam →
            -(l / lam) < z.1 u (Regeneration.Renewal.forceCoord hd))) := Iff.rfl
    simp only [hGk, hmemG]
    exact @ite_aux _ _ _ _ _ _
  · -- factorization for local `L^p` tests
    intro p hp F hFloc hFmem Φ hΦ hbΦ n ρ hρ
    by_cases hn : 2 * k ≤ n
    swap
    · have hempty : {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} = ∅ := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have hb := Regeneration.nat_two_step_le_regenerationTime
          (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) h₀ hR q.2
          (Regeneration.Renewal.forceCoord hd) k
        have h' : Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam
            (l / lam) q.2 (Regeneration.Renewal.forceCoord hd) k =
            (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := h
        rw [h'] at hb
        have h2 : (k : ℝ≥0) * (2 * Regeneration.Renewal.regenDelta lam) ≤
            (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam := by exact_mod_cast hb
        have h3 : ((2 * k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam ≤
            (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam := by
          calc ((2 * k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam
              = (k : ℝ≥0) * (2 * Regeneration.Renewal.regenDelta lam) := by push_cast; ring
            _ ≤ _ := h2
        have h4 := le_of_mul_le_mul_right h3 hΔ
        exact hn (by exact_mod_cast h4)
      rcases hρ with rfl | rfl <;> (rw [hempty]; simp)
    have hFg : Measurable F := hFloc.mono (Probability.localSigma_le_borel _) le_rfl
    have hsub : {x : Vec d | euclideanNorm x < A / lam} ⊆
        {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤ (10 * (k : ℝ) - 4) * (l / lam)} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have h1 := Regeneration.coordinate_abs_le_euclideanNorm x (Regeneration.Renewal.forceCoord hd)
      have hxk : (A / l + 4) / 10 ≤ (k : ℝ) := by
        have h5 : (⌈(A / l + 4) / 10⌉₊ : ℝ) ≤ (k : ℝ) := by
          rw [hkdef]
          exact_mod_cast le_max_right _ _
        exact (Nat.le_ceil _).trans h5
      have h6 : A / lam ≤ (10 * (k : ℝ) - 4) * (l / lam) := by
        calc A / lam = (A / l) * (l / lam) := by field_simp
          _ ≤ (10 * (k : ℝ) - 4) * (l / lam) :=
            mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hl.le h₀.le)
      have h7 := lt_of_le_of_lt ((le_abs_self _).trans h1) hx
      linarith
    let Fc : ℕ → FieldPair d → ℝ := fun N ω => max (-(N : ℝ)) (min (F ω) N)
    have hFcloc : ∀ N : ℕ, Measurable[localSigma {x : Vec d |
        x (Regeneration.Renewal.forceCoord hd) ≤ (10 * (k : ℝ) - 4) * (l / lam)}] (Fc N) := by
      intro N
      have hF' : Measurable[localSigma {x : Vec d |
          x (Regeneration.Renewal.forceCoord hd) ≤ (10 * (k : ℝ) - 4) * (l / lam)}] F :=
        hFloc.mono (Probability.localSigma_mono hsub) le_rfl
      exact measurable_const.max (hF'.min measurable_const)
    have hFcg : ∀ N : ℕ, Measurable (Fc N) := fun N =>
      (hFcloc N).mono (Probability.localSigma_le_borel _) le_rfl
    have hbFc : ∀ N : ℕ, Regeneration.BoundedRealTest (Fc N) := fun N =>
      ⟨N, fun ω => abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
        (min_le_right _ _)⟩⟩
    obtain ⟨M, hM⟩ := hbΦ
    have hFint : Integrable F Q.measure :=
      hFmem.integrable (ENNReal.one_le_ofReal.mpr (by linarith))
    have hint := integrable_fst_annealed Q K F hFg hFint
    have hDm : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0 :=
      hD
    let slice : Set (FieldPair d × CoupledSample d) := {q | regenerationTime hd lam l k q.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
    have key : ∀ (ρ' : Measure (FieldPair d × CoupledSample d))
        (hint' : Integrable (fun q : FieldPair d × CoupledSample d => F q.1) (ρ'.restrict slice))
        (c : ℝ), (∀ N : ℕ, (∫ q in slice, Fc N q.1 * Φ (regenerationRecord hd lam l k q) ∂ρ') =
          c * ∫ q in slice, Fc N q.1 ∂ρ') →
        (∫ q in slice, F q.1 * Φ (regenerationRecord hd lam l k q) ∂ρ') =
          c * ∫ q in slice, F q.1 ∂ρ' := by
      intro ρ' hint' c h
      exact limit_factor ρ' slice c (fun q => F q.1) (fun N q => Fc N q.1)
        (fun q => Φ (regenerationRecord hd lam l k q)) M
        (fun N => (hFcg N).comp measurable_fst)
        (hΦ.comp (Regeneration.measurable_cycleRecord hd lam l k))
        (fun q => hM _) (fun N q => abs_clip_le _ _ (N.cast_nonneg))
        (fun q => tendsto_clip _) hint' h
    rcases hρ with rfl | rfl
    · exact key _ hint.restrict _ (fun N =>
        bounded_factor_mu hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast hindep
          hprebridge k n hk1 hn (Fc N) (hFcloc N) (hbFc N) Φ hΦ ⟨M, hM⟩)
    · exact key _ (integrable_cond _ _ hD _ hint).restrict _ (fun N =>
        bounded_factor_nu hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast hindep
          hprebridge k n hk1 hn (Fc N) (hFcloc N) (hbFc N) Φ hΦ ⟨M, hM⟩)

end EinsteinFull.Blueprint
