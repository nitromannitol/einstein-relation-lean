import EinsteinFull.Blueprint.G1.Draft.SbxS6LocalMixingSmoothR01
import EinsteinFull.Blueprint.Foundation.Draft.SbxCFactorizationSmoothR01

/-! Conditional fixed-radius recurrence consumers for smooth laws. -/
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint.SbxCFixedRadiusRecurrencesR02
open EinsteinRelation EinsteinFull.Blueprint

theorem bounded_first_cycle_slice
    (hfact : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    {d : ℕ} (hd : 2 ≤ d) (SD : StructuralData d)
    (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (hQ : HasSmoothBounds SD Q)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : SD.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G)
    (hbF : Regeneration.BoundedRealTest F) (hbG : Regeneration.BoundedRealTest G)
    (n : ℕ) (u : ℝ≥0) (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hμ : μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d)))) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce q.1) *
        G (translate (q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam + u))
          (reduce q.1)) ∂μ) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce q.1) ∂μ) *
    ∫ q, G (translate (q.2.1 u) (reduce q.1))
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let Δ := Regeneration.Renewal.regenDelta lam
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  obtain ⟨D, hDm, hDr⟩ :=
    Probability.exists_future_halfSpace_decoder (Regeneration.Renewal.forceCoord hd) (l / lam)
  let Φ := PhiM Δ lam (l / lam) (Regeneration.Renewal.forceCoord hd) D G 0 u
  have hrec0 : ∀ᵐ q ∂ν, Φ (regenerationRecord hd lam l 0 q) =
      G (translate (q.2.1 u) (reduce q.1)) := by
    have hNB : ∀ᵐ q ∂ν,
        Regeneration.NoBacktracking (l / lam) q.2.1 (Regeneration.Renewal.forceCoord hd) :=
      ProbabilityTheory.ae_cond_mem
        ((Regeneration.measurableSet_NoBacktracking (l / lam)
          (Regeneration.Renewal.forceCoord hd)).preimage measurable_snd.fst)
    filter_upwards [hNB] with q hq
    have hrec : regenerationRecord hd lam l 0 q = Regeneration.futureRecord Δ (l / lam)
        q.1 q.2 (Regeneration.Renewal.forceCoord hd) 0 := by
      unfold regenerationRecord Regeneration.Renewal.cycleRecord
      rfl
    rw [hrec]
    have he := sbxS4_Phi0_record Δ lam (l / lam) _ D hDr G hG q.1 q.2 0 u
      (noBacktracking_pathTimeShift_zero _ _ _ hq)
    simpa only [zero_add] using he
  have hrec1 : ∀ q : FieldPair d × Regeneration.CoupledSample d,
      regenerationTime hd lam l 1 q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      Φ (regenerationRecord hd lam l 1 q) =
        G (translate (q.2.1 ((n : ℝ≥0) * Δ + u)) (reduce q.1)) := by
    intro q hq
    have hτ : Regeneration.regenerationTime Δ lam (l / lam) q.2
        (Regeneration.Renewal.forceCoord hd) 1 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hq
    have hNB := Regeneration.regenerationTime_succ_noBacktracking Δ hΔ lam (l / lam)
      q.2 (Regeneration.Renewal.forceCoord hd) 0
      (by rw [hτ]; exact ENNReal.coe_ne_top)
    rw [hτ, ENNReal.toNNReal_coe] at hNB
    have hrec : regenerationRecord hd lam l 1 q = Regeneration.futureRecord Δ (l / lam)
        q.1 q.2 (Regeneration.Renewal.forceCoord hd) ((n : ℝ≥0) * Δ) := by
      unfold regenerationRecord Regeneration.Renewal.cycleRecord
      rw [hτ, ENNReal.toNNReal_coe]
    rw [hrec]
    exact sbxS4_Phi0_record Δ lam (l / lam) _ D hDr G hG q.1 q.2 _ u hNB
  have hfa := (hfact d hd SD Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD).1
    (fun ω => F (reduce ω)) (hF.comp (Probability.measurable_reduce_local _))
    (by obtain ⟨C, hC⟩ := hbF; exact ⟨C, fun ω => hC (reduce ω)⟩)
    Φ (measurable_PhiM Δ lam (l / lam) (l / lam) _ D hDm G hG 0 u)
    (boundedRealTest_PhiM Δ lam (l / lam) _ D G hbG 0 u) n μ hμ
  have hTm : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l 1 q.2) :=
    (Regeneration.measurable_regenerationTime Δ lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) 1).comp measurable_snd
  calc
    _ = (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        F (reduce q.1) * Φ (regenerationRecord hd lam l 1 q) ∂μ) := by
      apply setIntegral_congr_ae (measurableSet_eq_fun hTm measurable_const)
      exact ae_of_all _ fun q hq => congrArg (F (reduce q.1) * ·) (hrec1 q hq).symm
    _ = _ := by rw [hfa, integral_congr_ae hrec0]


theorem first_cycle_slice_of_integrable
    (hfact : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : D.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G)
    (n : ℕ) (u : ℝ≥0) (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hμ : μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))))
    (hiF : Integrable (fun q => F (reduce q.1)) μ)
    (hiFG : Integrable (fun q => F (reduce q.1) *
      G (translate (q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam + u))
        (reduce q.1))) μ)
    (hiG : Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      G (translate (q.2.1 u) (reduce q.1)))
        (regenerationConditionedLaw hd Q lam l K hK.1 hD)) :
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce q.1) *
        G (translate (q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam + u))
          (reduce q.1)) ∂μ) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F (reduce q.1) ∂μ) *
    ∫ q, G (translate (q.2.1 u) (reduce q.1))
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let Fc := fun (j : ℕ) (ω : FieldPair d) => max (-(j : ℝ)) (min (j : ℝ) (F ω))
  let Gc := fun (j : ℕ) (ω : FieldPair d) => max (-(j : ℝ)) (min (j : ℝ) (G ω))
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hFr : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      F (reduce q.1)) := hFg.comp (Probability.measurable_reduce.comp measurable_fst)
  have hobs (v : ℝ≥0) : Measurable
      (fun q : FieldPair d × Regeneration.CoupledSample d =>
        G (translate (q.2.1 v) (reduce q.1))) :=
    hGg.comp (Probability.continuous_translate.measurable.comp
      (((continuous_eval_const v).measurable.comp measurable_snd.fst).prodMk
        (Probability.measurable_reduce.comp measurable_fst)))
  have hb (J : FieldPair d → ℝ) (j : ℕ) :
      Regeneration.BoundedRealTest (fun ω => max (-(j : ℝ)) (min (j : ℝ) (J ω))) := by
    refine ⟨(j : ℝ), fun ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩⟩
    exact max_le ((neg_nonpos.mpr (Nat.cast_nonneg j)).trans (Nat.cast_nonneg j))
      (min_le_left _ _)
  have heq (j : ℕ) := bounded_first_cycle_slice hfact hd D Q hQ lam h₀ h₁ l δ hl hsep
    hδ₀ hδ₁ P K hK hD (Fc j) (Gc j)
    (measurable_const.max (measurable_const.min hF))
    (measurable_const.max (measurable_const.min hG)) (hb F j) (hb G j) n u μ hμ
  have hleft := sbxS4_tendsto_setIntegral_mul_clamps μ _ _ hFr (hobs _) hiFG
    {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hGlim := tendsto_setIntegral_clamp
    (regenerationConditionedLaw hd Q lam l K hK.1 hD) _ hiG Set.univ
  simp only [Measure.restrict_univ] at hGlim
  have hright := (tendsto_setIntegral_clamp μ _ hiF
    {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}).mul
      hGlim
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun j => (heq j).symm))


theorem first_cycle_recurrence_of_integrable
    (hfact : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : D.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (F G : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hμ : μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))))
    (hiF : Integrable (fun q => F (reduce q.1)) μ)
    (hiFG : ∀ v : ℝ≥0, Integrable (fun q => F (reduce q.1) *
      G (translate (q.2.1 v) (reduce q.1))) μ)
    (hiG : ∀ v : ℝ≥0, Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      G (translate (q.2.1 v) (reduce q.1)))
        (regenerationConditionedLaw hd Q lam l K hK.1 hD))
    (s : ℝ≥0) (hs : s < Regeneration.Renewal.regenDelta lam) (k : ℕ) :
    (∫ q, F (reduce q.1) *
      G (translate (q.2.1 (s + k * Regeneration.Renewal.regenDelta lam)) (reduce q.1)) ∂μ) =
    (∫ q in {q | ((s + k * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) <
        regenerationTime hd lam l 1 q.2}, F (reduce q.1) *
      G (translate (q.2.1 (s + k * Regeneration.Renewal.regenDelta lam)) (reduce q.1)) ∂μ) +
    ∑ n ∈ Finset.range (k + 1),
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F (reduce q.1) ∂μ) *
      ∫ q, G (translate (q.2.1 (s + (k - n : ℕ) * Regeneration.Renewal.regenDelta lam))
        (reduce q.1)) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  rw [sbxS4_first_cycle_integral_partition hd lam l h₀ μ _ (hiFG _) s hs k]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnk : n ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have htime : (n : ℝ≥0) * Regeneration.Renewal.regenDelta lam +
      (s + (k - n : ℕ) * Regeneration.Renewal.regenDelta lam) =
      s + k * Regeneration.Renewal.regenDelta lam := by
    have hcast : (n : ℝ≥0) + ((k - n : ℕ) : ℝ≥0) = k := by
      exact_mod_cast Nat.add_sub_of_le hnk
    calc _ = s + ((n : ℝ≥0) + ((k - n : ℕ) : ℝ≥0)) *
        Regeneration.Renewal.regenDelta lam := by ring
      _ = _ := by rw [hcast]
  simpa only [htime] using
    first_cycle_slice_of_integrable hfact hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
      P K hK hD F G hF hG n (s + (k - n : ℕ) * Regeneration.Renewal.regenDelta lam)
      μ hμ hiF (hiFG _) (hiG _)

/-- The two fixed-radius recurrences under smooth factorization and remainder inputs. -/
theorem fixed_recurrences_of_smooth_deps
    (hfact : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmtV3) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (SD : StructuralData d),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ SD.dependenceRange < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d SD.ellipticity SD.dependenceRange) (_hQ : HasSmoothBounds SD Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let h := fun t : ℝ≥0 => ∫ q, G (translate (q.2.1 t) (reduce q.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ q in {q | (t : ℝ≥0∞) < regenerationTime hd lam l 1 q.2},
      G (translate (q.2.1 t) (reduce q.1)) ∂ν
    let hF := fun t : ℝ≥0 => ∫ q, F (reduce q.1) *
      G (translate (q.2.1 t) (reduce q.1)) ∂μ
    let rF := fun t : ℝ≥0 => ∫ q in {q | (t : ℝ≥0∞) < regenerationTime hd lam l 1 q.2},
      F (reduce q.1) * G (translate (q.2.1 t) (reduce q.1)) ∂μ
    let q := fun n : ℕ => ∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce q.1) ∂μ
    ∀ s : ℝ≥0, s < Δ → ∀ k : ℕ,
      h (s + k * Δ) = r (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), regenerationLatticeMass hd Q lam l K hK.1 hD n *
          h (s + (k - n : ℕ) * Δ) ∧
      hF (s + k * Δ) = rF (s + k * Δ) +
        ∑ n ∈ Finset.range (k + 1), q n * h (s + (k - n : ℕ) * Δ) := by
  intro d hd SD
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    SbxS6Section3R01.smooth_covariance_integrable hrem d hd SD
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro l δ hl hδ₀ hδ₁ Q hQ lam h₀ h₁ P K hK hD F G hF hG hFp hGp
  dsimp only
  intro s hs k
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let := reducedLaw_probability Q
  let : IsProbabilityMeasure ν := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hFg : Measurable F := hF.mono (Probability.localSigma_le_borel _) le_rfl
  have hGg : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hFi : Integrable F (reducedLaw Q) := hFp.integrable (by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    linarith)
  have hFr := (sbxS2_reducedFst_measurePreserving Q K hK.1).integrable_comp_of_integrable hFi
  have hiFG (v : ℝ≥0) := hInt Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD F G
    hFg hGg hFp hGp v μ (by simp [μ])
  have hiG (v : ℝ≥0) : Integrable
      (fun q : FieldPair d × Regeneration.CoupledSample d =>
        G (translate (q.2.1 v) (reduce q.1))) ν := by
    simpa only [one_mul] using hInt Q hQ lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
      (fun _ => 1) G measurable_const hGg (memLp_const 1) hGp v ν (by simp [ν])
  have hlpos := hl₀.trans_le hl
  have hsepl : SD.dependenceRange < 2 * l := hsep.trans_le (by linarith)
  constructor
  · have hh := first_cycle_recurrence_of_integrable hfact hd SD Q hQ lam h₀ h₁ l δ
      hlpos hsepl hδ₀ hδ₁ P K hK hD (fun _ => 1) G measurable_const hG ν
      (by simp [ν]) (integrable_const 1) (by simpa only [one_mul] using hiG) hiG s hs k
    have hmass (n : ℕ) :
        (∫ q in {q : FieldPair d × Regeneration.CoupledSample d |
          regenerationTime hd lam l 1 q.2 =
            (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          (1 : ℝ) ∂ν) = regenerationLatticeMass hd Q lam l K hK.1 hD n := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    simpa only [one_mul, hmass] using hh
  · exact first_cycle_recurrence_of_integrable hfact hd SD Q hQ lam h₀ h₁ l δ
      hlpos hsepl hδ₀ hδ₁ P K hK hD F G hF hG μ (by simp [μ]) hFr hiFG hiG s hs k

end EinsteinFull.Blueprint.SbxCFixedRadiusRecurrencesR02
