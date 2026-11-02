import EinsteinFull.Blueprint.G1.Draft.SbxCKFactorBoundedSmoothR02
import EinsteinFull.Blueprint.G1.Draft.SbxCKFactorDisintegrationSmoothR02
import EinsteinFull.Blueprint.G1.Draft.SbxCKMCovarianceSmoothR01
import EinsteinRelation.Regeneration.CycleRecordMeasurability

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion)

open EinsteinFull.Work.W5
open EinsteinFull.Blueprint.SbxS5Section3R01

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat


private theorem ite_aux_smooth_assembly (P1 P2 P3 : Prop) [Decidable (P1 ∧ P2 ∧ P3)] [Decidable (P1 ∧ P3)]
    [Decidable P2] :
    (if P1 ∧ P2 ∧ P3 then (1 : ℝ) else 0) = (if P1 ∧ P3 then (1 : ℝ) else 0) *
      (if P2 then (1 : ℝ) else 0) := by
  by_cases h1 : P1 <;> by_cases h2 : P2 <;> by_cases h3 : P3 <;> simp [h1, h2, h3]

/-- Uniform k-factor contract with its constant independent of derivative bounds. -/
def kmKFactorUniformSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (_hΛ : 1 ≤ Λ₀) (_hr : 1 ≤ r₀)
    (l δ : ℝ) (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ₀ : 0 < δ) (_hδ₁ : δ < 1),
  ∃ C : ℝ, 0 < C ∧
  ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
  let D : StructuralData d := ⟨Λ₀, r₀, β, _hΛ, _hr, hβ⟩
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
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
  ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd R) ≠ 0,
  ∀ A : ℝ, l ≤ A →
    let k := max 1 ⌈(A / l + 4) / 10⌉₊
    (k : ℝ) ≤ C * (1 + A) ∧
    (∀ n : ℕ, 2 * k ≤ n → ∀ y : Vec d, ∀ b : Bool,
      ∃ V : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] V ∧
        (fun ω => ∫ z,
          (if z ∈ Γ k n ∧
              y ∈ Regeneration.endpointBall i R (z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ)) ∧
              (b = true → ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
                -R < z.1 u i)
            then (1 : ℝ) else 0) ∂K (0, ω)) =ᵐ[Q.measure] V) ∧
    ∀ (p : ℝ), 2 ≤ p → ∀ F : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
      MemLp F (ENNReal.ofReal p) Q.measure →
      ∀ Φ : Regeneration.FutureState d i R → ℝ,
        Measurable Φ → Regeneration.BoundedRealTest Φ → ∀ n : ℕ,
      ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
            (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F ωz.1 * Φ (regenerationRecord hd lam l k ωz) ∂μ) =
        (∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
        ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
            (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F ωz.1 ∂μ

theorem kFactorUniformSmooth_of_deps
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : SbxCFactorizationR01.pastKernelSmoothStmt)
    (hindep : SbxCFactorizationR01.independenceSmoothStmt)
    (hprebridge : prebridgeKSmoothStmt) :
    kmKFactorUniformSmoothStmt := by
  classical
  have hdis : sliceDisintegrationInputStmt := by
    intro d hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn G hG hbG hGΓ F hF hbF Φ hΦ hbΦ
    exact slice_k_disintegration_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
      hprebridge k n hk hn G hG hbG hGΓ F hF hbF Φ hΦ hbΦ
  intro d hd Λ₀ r₀ hΛ hr l δ hl hsep hδ₀ hδ₁
  refine ⟨3 + 1 / l, by positivity, ?_⟩
  intro β hβ D Q hQ lam h₀ h₁ P K hK
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
    obtain ⟨A', hA', hAe⟩ := AyK_local_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hgeom hpast k n
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
    exact @ite_aux_smooth_assembly _ _ _ _ _ _
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
        bounded_factor_mu_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast hindep
          hdis k n hk1 hn (Fc N) (hFcloc N) (hbFc N) Φ hΦ ⟨M, hM⟩)
    · exact key _ (integrable_cond _ _ hD _ hint).restrict _ (fun N =>
        bounded_factor_nu_smooth hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast hindep
          hdis k n hk1 hn (Fc N) (hFcloc N) (hbFc N) Φ hΦ ⟨M, hM⟩)

end
end EinsteinFull.Blueprint
