import EinsteinRelation.Probability.FiniteHistorySplit

/-!
# Closed spatial constraints on exact finite histories

Source `paper/main.tex:377–381`. These are the path restrictions used
when iterating the one-interval locality identities. They are measurable
in the literal finite history and split at deterministic grid times.
-/

open MeasureTheory EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinRelation.Probability

/-- The actual path remains in a fixed spatial set through the grid endpoint. -/
def historyStays {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (V : Set (Vec d)) :
    Set (CoupledSample d) :=
  {z | ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → z.1 t ∈ V}

/-- A closed spatial barrier is a closed event on the continuous-path carrier. -/
theorem isClosed_historyStays {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (V : Set (Vec d)) (hV : IsClosed V) : IsClosed (historyStays Δ n V) := by
  have heq : historyStays Δ n V =
      ⋂ (t : ℝ≥0) (_ : t ≤ (n : ℝ≥0) * Δ), (fun z : CoupledSample d => z.1 t) ⁻¹' V := by
    ext z
    simp only [historyStays, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    hV.preimage ((continuous_eval_const t).comp continuous_fst)

/-- Closed path constraints through `nΔ` are measurable in the exact finite history. -/
theorem measurableSet_historyStays {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (V : Set (Vec d)) (hV : IsClosed V) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n) (historyStays Δ n V) := by
  have heq : historyStays Δ n V = stoppedHistorySample Δ n ⁻¹' historyStays Δ n V := by
    ext z
    simp only [historyStays, Set.mem_setOf_eq, Set.mem_preimage]
    exact forall_congr' fun t => imp_congr_right fun ht => by
      rw [stoppedHistorySample_path Δ n z t ht]
  rw [heq]
  exact (measurable_stoppedHistorySample Δ n) ((isClosed_historyStays Δ n V hV).measurableSet)

/-- A stopped history stays in the barrier exactly when the original history does. -/
theorem stoppedHistorySample_mem_historyStays_iff {d : ℕ}
    (Δ : ℝ≥0) (n : ℕ) (V : Set (Vec d)) (z : CoupledSample d) :
    stoppedHistorySample Δ n z ∈ historyStays Δ n V ↔ z ∈ historyStays Δ n V := by
  simp only [historyStays, Set.mem_setOf_eq]
  exact forall_congr' fun t => imp_congr_right fun ht => by
    rw [stoppedHistorySample_path Δ n z t ht]

/-- The complete closed barrier constraint splits into the actual past
constraint and the constraint on the shifted last interval. -/
theorem mem_historyStays_succ_iff {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (V : Set (Vec d)) (z : CoupledSample d) :
    z ∈ historyStays Δ (n + 1) V ↔ z ∈ historyStays Δ n V ∧
      sampleTimeShift Δ z ((n : ℝ≥0) * Δ) ∈ historyStays Δ 1 V := by
  have hgrid : ((n + 1 : ℕ) : ℝ≥0) * Δ = (n : ℝ≥0) * Δ + Δ := by
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  change (∀ t : ℝ≥0, t ≤ _ → z.1 t ∈ V) ↔
    (∀ t : ℝ≥0, t ≤ _ → z.1 t ∈ V) ∧
      (∀ t : ℝ≥0, t ≤ _ → z.1 ((n : ℝ≥0) * Δ + t) ∈ V)
  simp only [hgrid, Nat.cast_one, one_mul]
  constructor
  · intro h
    exact ⟨fun t ht => h t (ht.trans (le_add_of_nonneg_right zero_le)),
      fun t ht => h _ (add_le_add le_rfl ht)⟩
  · rintro ⟨hp, hf⟩ t ht
    by_cases htn : t ≤ (n : ℝ≥0) * Δ
    · exact hp t htn
    · have hle : t - (n : ℝ≥0) * Δ ≤ Δ := by
        rw [tsub_le_iff_right]
        exact ht.trans_eq (add_comm _ _)
      have h := hf _ hle
      rwa [add_tsub_cancel_of_le (not_le.mp htn).le] at h


end EinsteinRelation.Probability
