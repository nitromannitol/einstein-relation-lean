import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The finite failed-guard prefix is measurable at the next even passage. -/
theorem guard_prefix_stopped_measurable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (i : Fin d) (N : ℕ) :
    let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
    let hT := coupling_scope_isStoppingTime_passageSequence Δ hΔ lam R a hR i (2 * N)
    MeasurableSet[hT.measurableSpace] {γ | T γ < ⊤ ∧ ∀ r < N,
      Regeneration.passageSequence Δ lam R a γ i (2 * r) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * r)} := by
  let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
  let E : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ r < N,
    Regeneration.passageSequence Δ lam R a γ i (2 * r) ≠ ⊤ ∧
      ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * r)}
  let F := MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)
  let hT := coupling_scope_isStoppingTime_passageSequence Δ hΔ lam R a hR i (2 * N)
  have hE : MeasurableSet E := by
    dsimp only [E, T, Set.ofPred_and]
    apply (measurableSet_lt ((Regeneration.measurable_passageSequence_joint Δ lam R i (2 * N)).comp
      (measurable_const.prodMk measurable_id)) measurable_const).inter
    have hprefix : MeasurableSet (⋂ r : ℕ, ⋂ (_ : r < N),
        {γ : Path d | Regeneration.passageSequence Δ lam R a γ i (2 * r) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * r)}) := by
      apply MeasurableSet.iInter
      intro r
      apply MeasurableSet.iInter
      intro hr
      exact (measurableSet_eq_fun ((Regeneration.measurable_passageSequence_joint Δ lam R i (2 * r)).comp
        (measurable_const.prodMk measurable_id)) measurable_const).compl.inter
        (((measurable_const.prodMk measurable_id) (Regeneration.measurableSet_IsGoodPassage Δ lam R i (2 * r))).compl)
    convert hprefix using 1
    ext γ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  have hsup : borel (Path d) ≤ ⨆ t, F t := by
    letI : MeasurableSpace (Path d) := ⨆ t, F t
    have hid : @Measurable (Path d) (Path d) (⨆ t, F t) (borel (Path d)) id := by
      apply ContinuousMap.measurable_iff_eval.mpr
      intro t
      exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := Vec d) t).mono (le_iSup F t) le_rfl
    simpa only [MeasurableSpace.comap_id] using hid.comap_le
  change MeasurableSet[hT.measurableSpace] E
  change MeasurableSet[⨆ t, F t] E ∧ ∀ t : ℝ≥0,
    MeasurableSet[F t] (E ∩ {γ | T γ ≤ (t : ℝ≥0∞)})
  constructor
  · exact hsup E hE
  · intro t
    let S : Path d → Path d := MarkovProcess.ContinuousPath.stoppedPath t
    have heq : E ∩ {γ | T γ ≤ (t : ℝ≥0∞)} = S ⁻¹' E ∩ {γ | T γ ≤ (t : ℝ≥0∞)} := by
      ext γ
      have hpre : ∀ u ∈ Set.Icc (0 : ℝ≥0) t, γ u = S γ u :=
        fun u hu => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le t γ u hu.2).symm
      have hp := Regeneration.passageSequence_prefix_determined Δ hΔ lam R a hR γ (S γ) i (2 * N) t hpre
      have hlocal (x y : Path d) (hxy : ∀ u ∈ Set.Icc (0 : ℝ≥0) t, x u = y u)
          (ht : Regeneration.passageSequence Δ lam R a x i (2 * N) ≤ (t : ℝ≥0∞)) :
          x ∈ E → y ∈ E := by
        intro hx
        have hnext := (Regeneration.passageSequence_prefix_determined Δ hΔ lam R a hR x y i (2 * N) t hxy).2 ht
        refine ⟨?_, fun r hr => ?_⟩
        · change Regeneration.passageSequence Δ lam R a y i (2 * N) < ⊤
          rw [← hnext]
          exact hx.1
        · have hmono := Regeneration.monotone_passageSequence Δ hΔ lam R a hR x i
          have hfin : Regeneration.passageSequence Δ lam R a x i (2 * N) ≠ ⊤ := ne_of_lt hx.1
          have hrfin := ne_top_of_le_ne_top hfin (hmono (by omega : 2 * r ≤ 2 * N))
          have hurfin : Regeneration.roundUp Δ (Regeneration.passageSequence Δ lam R a x i (2 * r)) ≠ ⊤ := by
            rw [Regeneration.roundUp, if_neg hrfin]
            exact ENNReal.coe_ne_top
          have hu : Regeneration.roundUp Δ (Regeneration.passageSequence Δ lam R a x i (2 * r)) ≤ (t : ℝ≥0∞) :=
            (Regeneration.rounded_passage_lt_next Δ lam R a hR x i (2 * r) hurfin).le.trans
              ((hmono (by omega : 2 * r + 1 ≤ 2 * N)).trans ht)
          have hv := (Regeneration.le_roundUp Δ hΔ _).trans hu
          have hpass := (Regeneration.passageSequence_prefix_determined Δ hΔ lam R a hR x y i (2 * r) t hxy).2 hv
          have hvt : (Regeneration.passageSequence Δ lam R a x i (2 * r)).toNNReal ≤ t :=
            ENNReal.coe_le_coe.mp (by rwa [ENNReal.coe_toNNReal hrfin])
          have hut : (Regeneration.roundUp Δ (Regeneration.passageSequence Δ lam R a x i (2 * r))).toNNReal ≤ t :=
            ENNReal.coe_le_coe.mp (by rwa [ENNReal.coe_toNNReal hurfin])
          refine ⟨?_, ?_⟩
          · rw [← hpass]; exact hrfin
          · intro hy
            apply (hx.2 r hr).2
            unfold Regeneration.IsGoodPassage at hy ⊢
            rw [← hpass] at hy
            refine ⟨hy.1, hy.2.1, fun u hu' => ?_⟩
            rw [hxy u ⟨zero_le, hu'.2.trans hut⟩, hxy _ ⟨zero_le, hvt⟩]
            exact hy.2.2 u hu'
      constructor
      · rintro ⟨hx, ht⟩
        exact ⟨hlocal γ (S γ) hpre ht hx, ht⟩
      · rintro ⟨hy, ht⟩
        have hty : T (S γ) ≤ (t : ℝ≥0∞) := (hp.1).mp ht
        exact ⟨hlocal (S γ) γ (fun u hu => (hpre u hu).symm) hty hy, ht⟩
    rw [heq]
    exact ((coupling_scope_measurable_stoppedPath_history t) hE).inter (hT t)

end EinsteinFull.Blueprint
