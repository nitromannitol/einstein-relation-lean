import EinsteinFull.Blueprint.G1.node_rt_u3A_prebridge_u2D_k
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinRelation.Regeneration.OneIntervalBridgeSupport
import EinsteinRelation.Regeneration.NoBacktrackingPrefix
import EinsteinRelation.Regeneration.ForcedBitGeometry
import EinsteinRelation.Regeneration.FiniteHistoryTrialEvent
import EinsteinRelation.Regeneration.TrialBounds
import EinsteinRelation.Regeneration.RegenerationGrid
import EinsteinRelation.Regeneration.RenewalRecordIteration
import EinsteinRelation.Probability.FiniteHistoryFiltration

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime
  couplingRegion gridIndex)

/-! # `rt:prebridge-k`

The finite union of tuple events, its exact finite-history measurability, and the
almost-sure identification of the `k`-th regeneration slice. -/

/-- The literal tuple event of `node_rt_u3A_prebridge_u2D_kStmt`. -/
abbrev tupleEventS {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k n : ℕ)
    (a : Fin (k + 1) → ℕ) : Set (CoupledSample d) :=
  {z : CoupledSample d |
    a 0 = 0 ∧ a (Fin.last k) = n ∧
    (∀ j : Fin k, a j.castSucc + 2 ≤ a j.succ) ∧
    (∀ j : Fin k,
      sampleTimeShift Δ z ((a j.castSucc : ℝ≥0) * Δ) ∈
        forcedBitTrialEvent Δ lam R i (a j.succ - a j.castSucc - 1)) ∧
    (∀ j : Fin k, j.val + 1 < k → z.2 (a j.succ - 1) = true) ∧
    (∀ j : Fin k, j.val + 1 < k → ∀ u : ℝ≥0,
      (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
      z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i)}

/-- The finite union over bounded tuples. -/
abbrev tupleUnionS {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k n : ℕ) :
    Set (CoupledSample d) :=
  ⋃ a : Fin (k + 1) → Fin (n + 1), tupleEventS Δ lam R i k n (fun j => (a j).val)

/-- The same tuple conditions, indexed by natural numbers. -/
def TupleN {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k n : ℕ) (b : ℕ → ℕ)
    (z : CoupledSample d) : Prop :=
  b 0 = 0 ∧ b k = n ∧ (∀ j < k, b j + 2 ≤ b (j + 1)) ∧
  (∀ j < k, sampleTimeShift Δ z ((b j : ℝ≥0) * Δ) ∈
    forcedBitTrialEvent Δ lam R i (b (j + 1) - b j - 1)) ∧
  (∀ j < k, j + 1 < k → z.2 (b (j + 1) - 1) = true) ∧
  (∀ j < k, j + 1 < k → ∀ u : ℝ≥0,
    (b (j + 1) : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
    z.1 ((b (j + 1) : ℝ≥0) * Δ) i - R < z.1 u i)

theorem tupleEventS_iff {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k n : ℕ)
    (b : ℕ → ℕ) (z : CoupledSample d) :
    z ∈ tupleEventS Δ lam R i k n (fun j : Fin (k + 1) => b j.val) ↔
      TupleN Δ lam R i k n b z := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    refine ⟨by simpa using h0, by simpa using h1, fun j hj => ?_, fun j hj => ?_,
      fun j hj hj1 => ?_, fun j hj hj1 u hu1 hu2 => ?_⟩
    · simpa using h2 ⟨j, hj⟩
    · simpa using h3 ⟨j, hj⟩
    · simpa using h4 ⟨j, hj⟩ hj1
    · simpa using h5 ⟨j, hj⟩ hj1 u hu1 hu2
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    refine ⟨by simpa using h0, by simpa using h1, fun j => ?_, fun j => ?_,
      fun j hj1 => ?_, fun j hj1 u hu1 hu2 => ?_⟩
    · simpa using h2 j.val j.isLt
    · simpa using h3 j.val j.isLt
    · simpa using h4 j.val j.isLt hj1
    · simpa using h5 j.val j.isLt hj1 u hu1 hu2

theorem pathTimeShift_shift {d : ℕ} (γ : Path d) (s t : ℝ≥0) :
    pathTimeShift (pathTimeShift γ s) t = pathTimeShift γ (s + t) := by
  ext u i
  change γ (s + (t + u)) i = γ ((s + t) + u) i
  rw [add_assoc]

/-! ## Finite-history measurability -/

theorem measurable_shift_finiteHistory {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (a m : ℕ) :
    @Measurable (CoupledSample d) (CoupledSample d) (finiteHistorySigma Δ (a + m))
      (finiteHistorySigma Δ m) (fun z => sampleTimeShift Δ z ((a : ℝ≥0) * Δ)) := by
  apply Measurable.of_comap_le
  unfold finiteHistorySigma
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup, MeasurableSpace.comap_iSup]
  refine sup_le (le_sup_of_le_left (iSup_le fun t => ?_))
    (le_sup_of_le_right (iSup_le fun k => ?_))
  · rw [MeasurableSpace.comap_comp]
    refine le_iSup_of_le (⟨(a : ℝ≥0) * Δ + (t : ℝ≥0), zero_le, ?_⟩ :
      Set.Icc (0 : ℝ≥0) (((a + m : ℕ) : ℝ≥0) * Δ)) ?_
    · have ht := (Set.mem_Icc.mp t.2).2
      calc (a : ℝ≥0) * Δ + (t : ℝ≥0) ≤ (a : ℝ≥0) * Δ + (m : ℝ≥0) * Δ :=
            add_le_add le_rfl ht
        _ = ((a + m : ℕ) : ℝ≥0) * Δ := by rw [Nat.cast_add, add_mul]
    · exact le_of_eq rfl
  · rw [MeasurableSpace.comap_comp]
    refine le_iSup_of_le (⟨a + (k : ℕ), by have := k.2; omega⟩ : {j : ℕ // j < a + m}) ?_
    refine le_of_eq (congrArg (fun g => MeasurableSpace.comap g inferInstance) ?_)
    funext z
    change z.2 (gridIndex Δ ((a : ℝ≥0) * Δ) + (k : ℕ)) = z.2 (a + (k : ℕ))
    rw [Regeneration.gridIndex_mul Δ hΔ]

theorem measurableSet_bit_true {d : ℕ} (Δ : ℝ≥0) (N m : ℕ) (hm : m < N) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ N) {z | z.2 m = true} := by
  have hmeas : @Measurable (CoupledSample d) Bool (finiteHistorySigma Δ N) inferInstance
      (fun z => z.2 m) := by
    apply Measurable.of_comap_le
    exact le_sup_of_le_right (le_iSup_of_le (⟨m, hm⟩ : {k : ℕ // k < N}) le_rfl)
  exact hmeas (measurableSet_singleton true)

theorem measurableSet_survival {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d)
    (s N : ℕ) (hsN : s ≤ N) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ N)
      {z | ∀ u : ℝ≥0, (s : ℝ≥0) * Δ ≤ u → u ≤ (N : ℝ≥0) * Δ →
        z.1 ((s : ℝ≥0) * Δ) i - R < z.1 u i} := by
  have hN : s + (N - s) = N := by omega
  have hsh := measurable_shift_finiteHistory (d := d) Δ hΔ s (N - s)
  rw [hN] at hsh
  have hpre := hsh (Regeneration.measurableSet_noBacktracking_prefix Δ (N - s) R i)
  have hsum : (s : ℝ≥0) * Δ + ((N - s : ℕ) : ℝ≥0) * Δ = (N : ℝ≥0) * Δ := by
    rw [← add_mul, ← Nat.cast_add, hN]
  convert hpre using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  have e0 : (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)).1 0 i = z.1 ((s : ℝ≥0) * Δ) i := by
    change z.1 ((s : ℝ≥0) * Δ + 0) i = _
    rw [add_zero]
  constructor
  · intro h t ht
    have hle : (s : ℝ≥0) * Δ + t ≤ (N : ℝ≥0) * Δ := by
      rw [← hsum]
      exact add_le_add le_rfl ht
    have h' := h ((s : ℝ≥0) * Δ + t) (le_add_of_nonneg_right zero_le) hle
    have e1 : (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)).1 t i = z.1 ((s : ℝ≥0) * Δ + t) i := rfl
    rw [e1, e0]
    linarith
  · intro h u hu1 hu2
    have ht : u - (s : ℝ≥0) * Δ ≤ ((N - s : ℕ) : ℝ≥0) * Δ := by
      rw [tsub_le_iff_left, hsum]
      exact hu2
    have h' := h (u - (s : ℝ≥0) * Δ) ht
    have e1 : (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)).1 (u - (s : ℝ≥0) * Δ) i = z.1 u i := by
      change z.1 ((s : ℝ≥0) * Δ + (u - (s : ℝ≥0) * Δ)) i = _
      rw [add_tsub_cancel_of_le hu1]
    rw [e1, e0] at h'
    linarith

theorem measurableSet_tupleEventS {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (i : Fin d) (k n : ℕ) (a : Fin (k + 1) → ℕ) (ha : ∀ j, a j ≤ n) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ (n - 1))
      (tupleEventS Δ lam R i k n a) := by
  letI : MeasurableSpace (CoupledSample d) := finiteHistorySigma Δ (n - 1)
  by_cases h0 : a 0 = 0
  swap
  · have : tupleEventS Δ lam R i k n a = ∅ := by
      ext z; simp [h0]
    rw [this]; exact MeasurableSet.empty
  by_cases h1 : a (Fin.last k) = n
  swap
  · have : tupleEventS Δ lam R i k n a = ∅ := by
      ext z; simp [h1]
    rw [this]; exact MeasurableSet.empty
  by_cases h2 : ∀ j : Fin k, a j.castSucc + 2 ≤ a j.succ
  swap
  · have : tupleEventS Δ lam R i k n a = ∅ := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact h2 h.2.2.1
    rw [this]; exact MeasurableSet.empty
  have hfin : ∀ j : Fin k, j.val + 1 < k → a j.succ + 2 ≤ n := by
    intro j hjk
    have hnext := h2 ⟨j.val + 1, hjk⟩
    have e : (⟨j.val + 1, hjk⟩ : Fin k).castSucc = j.succ := by ext; simp
    rw [e] at hnext
    have h3 := ha (⟨j.val + 1, hjk⟩ : Fin k).succ
    omega
  have h4 : MeasurableSet {z : CoupledSample d | ∀ j : Fin k,
      sampleTimeShift Δ z ((a j.castSucc : ℝ≥0) * Δ) ∈
        forcedBitTrialEvent Δ lam R i (a j.succ - a j.castSucc - 1)} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => ?_
    have hj := h2 j
    have hle : a j.castSucc + (a j.succ - a j.castSucc - 1) ≤ n - 1 := by
      have := ha j.succ; omega
    have hm := Regeneration.measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i
      (a j.succ - a j.castSucc - 1)
    have hs := measurable_shift_finiteHistory (d := d) Δ hΔ (a j.castSucc)
      (a j.succ - a j.castSucc - 1) hm
    exact (Regeneration.finiteHistorySigma_mono Δ hle) _ hs
  have h5 : MeasurableSet {z : CoupledSample d | ∀ j : Fin k, j.val + 1 < k →
      z.2 (a j.succ - 1) = true} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => ?_
    by_cases hjk : j.val + 1 < k
    · have hlt : a j.succ - 1 < n - 1 := by
        have := hfin j hjk
        have hpos := h2 j
        omega
      have hb := measurableSet_bit_true (d := d) Δ (n - 1) (a j.succ - 1) hlt
      have hs : {z : CoupledSample d | j.val + 1 < k → z.2 (a j.succ - 1) = true} =
          {z | z.2 (a j.succ - 1) = true} := by
        ext z; simp [hjk]
      rw [hs]; exact hb
    · have hs : {z : CoupledSample d | j.val + 1 < k → z.2 (a j.succ - 1) = true} =
          Set.univ := by
        ext z; simp [hjk]
      rw [hs]; exact MeasurableSet.univ
  have h6 : MeasurableSet {z : CoupledSample d | ∀ j : Fin k, j.val + 1 < k →
      ∀ u : ℝ≥0, (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
        z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => ?_
    by_cases hjk : j.val + 1 < k
    · have hle : a j.succ ≤ n - 1 := by have := hfin j hjk; omega
      have hs := measurableSet_survival (d := d) Δ hΔ R i (a j.succ) (n - 1) hle
      have he : {z : CoupledSample d | j.val + 1 < k → ∀ u : ℝ≥0,
          (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
          z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i} =
          {z | ∀ u : ℝ≥0, (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
          z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i} := by
        ext z; simp [hjk]
      rw [he]; exact hs
    · have he : {z : CoupledSample d | j.val + 1 < k → ∀ u : ℝ≥0,
          (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
          z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i} = Set.univ := by
        ext z; simp [hjk]
      rw [he]; exact MeasurableSet.univ
  have hset : tupleEventS Δ lam R i k n a =
      {z | ∀ j : Fin k, sampleTimeShift Δ z ((a j.castSucc : ℝ≥0) * Δ) ∈
        forcedBitTrialEvent Δ lam R i (a j.succ - a j.castSucc - 1)} ∩
      ({z | ∀ j : Fin k, j.val + 1 < k → z.2 (a j.succ - 1) = true} ∩
      {z | ∀ j : Fin k, j.val + 1 < k → ∀ u : ℝ≥0,
        (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
        z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i}) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨_, _, _, x, y, w⟩
      exact ⟨x, y, w⟩
    · rintro ⟨x, y, w⟩
      exact ⟨h0, h1, h2, x, y, w⟩
  rw [hset]
  exact MeasurableSet.inter h4 (MeasurableSet.inter h5 h6)

theorem measurableSet_tupleUnionS {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R)
    (i : Fin d) (k n : ℕ) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ (n - 1))
      (tupleUnionS Δ lam R i k n) := by
  letI : MeasurableSpace (CoupledSample d) := finiteHistorySigma Δ (n - 1)
  refine MeasurableSet.iUnion fun a => ?_
  exact measurableSet_tupleEventS Δ hΔ lam R hR i k n _
    (fun j => Nat.lt_succ_iff.mp (a j).isLt)

/-! ## Regeneration iterates and single cycles -/

/-- The deterministic first-slice characterization (the node `app:factorization#slices`),
at general sample points. -/
def SliceChar {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ z : CoupledSample d,
    firstRegenerationTime Δ lam R z i = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔
      (z ∈ forcedBitTrialEvent Δ lam R i (m - 1) ∧ z.2 (m - 1) = true ∧
        NoBacktracking R (pathTimeShift z.1 ((m : ℝ≥0) * Δ)) i)

/-- One regeneration cycle from grid index `s` to grid index `e`. -/
def CycleOK {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (z : CoupledSample d)
    (s e : ℕ) : Prop :=
  sampleTimeShift Δ z ((s : ℝ≥0) * Δ) ∈ forcedBitTrialEvent Δ lam R i (e - s - 1) ∧
  z.2 (e - 1) = true ∧ NoBacktracking R (pathTimeShift z.1 ((e : ℝ≥0) * Δ)) i

theorem cycle_iff {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hs : SliceChar Δ lam R i) (z : CoupledSample d) (s e : ℕ) (hse : s + 2 ≤ e) :
    firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)) i =
        ((((e - s : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔ CycleOK Δ lam R i z s e := by
  rw [hs (e - s) (by omega)]
  have hcoin : (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)).2 (e - s - 1) = z.2 (e - 1) := by
    change z.2 (gridIndex Δ ((s : ℝ≥0) * Δ) + (e - s - 1)) = z.2 (e - 1)
    rw [Regeneration.gridIndex_mul Δ hΔ]
    exact congrArg z.2 (by omega)
  have hpath : pathTimeShift (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)).1
      (((e - s : ℕ) : ℝ≥0) * Δ) = pathTimeShift z.1 ((e : ℝ≥0) * Δ) := by
    change pathTimeShift (pathTimeShift z.1 ((s : ℝ≥0) * Δ)) _ = _
    rw [pathTimeShift_shift, ← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' (by omega)]
  unfold CycleOK
  rw [hcoin, hpath]

theorem regenerationTime_ne_top_of_le {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (z : CoupledSample d)
    (i : Fin d) {j k : ℕ} (hjk : j ≤ k)
    (h : Regeneration.regenerationTime Δ lam R z i k ≠ ⊤) :
    Regeneration.regenerationTime Δ lam R z i j ≠ ⊤ := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this
    exact h
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · exact h
    · apply ih (by omega)
      intro ht
      apply h
      rw [Regeneration.regenerationTime, if_pos ht]

theorem exists_indices {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (z : CoupledSample d)
    (i : Fin d) (k : ℕ) (h : Regeneration.regenerationTime Δ lam R z i k ≠ ⊤) :
    ∃ b : ℕ → ℕ, ∀ j ≤ k,
      Regeneration.regenerationTime Δ lam R z i j = (((b j : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  have hex : ∀ j, ∃ c : ℕ, j ≤ k →
      Regeneration.regenerationTime Δ lam R z i j = (((c : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨c, hc⟩ := Regeneration.regenerationTime_mem_grid Δ hΔ lam R z i j
        (regenerationTime_ne_top_of_le Δ lam R z i hj h)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose b hb using hex
  exact ⟨b, fun j hj => hb j hj⟩

theorem regenerationTime_succ_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (z : CoupledSample d) (i : Fin d) (j s e : ℕ)
    (hj : Regeneration.regenerationTime Δ lam R z i j = (((s : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (hj1 : Regeneration.regenerationTime Δ lam R z i (j + 1) =
      (((e : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    s + 2 ≤ e ∧ firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)) i =
      ((((e - s : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  have hne : Regeneration.regenerationTime Δ lam R z i j ≠ ⊤ := by
    rw [hj]; exact ENNReal.coe_ne_top
  have hexp : Regeneration.regenerationTime Δ lam R z i (j + 1) =
      Regeneration.regenerationTime Δ lam R z i j + firstRegenerationTime Δ lam R
        (sampleTimeShift Δ z (Regeneration.regenerationTime Δ lam R z i j).toNNReal) i := by
    rw [Regeneration.regenerationTime, if_neg hne]
  rw [hj, ENNReal.toNNReal_coe, hj1] at hexp
  have hFtop : firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)) i ≠ ⊤ := by
    intro h
    rw [h, add_top] at hexp
    exact ENNReal.coe_ne_top hexp
  obtain ⟨c, hc⟩ := Regeneration.firstRegenerationTime_mem_grid Δ hΔ lam R _ i hFtop
  have h2 := Regeneration.two_step_le_firstRegenerationTime Δ hΔ lam R hlam hR
    (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)) i
  rw [hc] at h2 hexp
  have hsum : ((e : ℝ≥0) * Δ) = ((s : ℝ≥0) * Δ) + ((c : ℝ≥0) * Δ) := by
    have h3 : (((e : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) =
        (((s : ℝ≥0) * Δ + (c : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_add]; exact hexp
    exact ENNReal.coe_injective h3
  have hec : e = s + c := by
    have h4 : (e : ℝ≥0) * Δ = ((s + c : ℕ) : ℝ≥0) * Δ := by
      rw [hsum, Nat.cast_add, add_mul]
    exact_mod_cast mul_right_cancel₀ hΔ.ne' h4
  have hc2 : 2 ≤ c := by
    have h5 : (2 : ℝ≥0) * Δ ≤ (c : ℝ≥0) * Δ := by exact_mod_cast h2
    exact_mod_cast le_of_mul_le_mul_right h5 hΔ
  refine ⟨by omega, ?_⟩
  rw [hc]
  have : e - s = c := by omega
  rw [this]

theorem regenerationTime_succ_of_first {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (z : CoupledSample d)
    (i : Fin d) (j s e : ℕ)
    (hj : Regeneration.regenerationTime Δ lam R z i j = (((s : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (hse : s ≤ e)
    (hF : firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)) i =
      ((((e - s : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    Regeneration.regenerationTime Δ lam R z i (j + 1) = (((e : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  have hne : Regeneration.regenerationTime Δ lam R z i j ≠ ⊤ := by
    rw [hj]; exact ENNReal.coe_ne_top
  rw [Regeneration.regenerationTime, if_neg hne, hj, ENNReal.toNNReal_coe, hF,
    ← ENNReal.coe_add, ← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hse]

/-! ## The forward direction (deterministic) -/

theorem forward_of_time {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam)
    (hR : 0 < R) (i : Fin d) (hs : SliceChar Δ lam R i) (z : CoupledSample d)
    (k n : ℕ) (hk : 1 ≤ k)
    (h : Regeneration.regenerationTime Δ lam R z i k = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    ∃ b : ℕ → ℕ, (∀ j ≤ k, Regeneration.regenerationTime Δ lam R z i j =
        (((b j : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) ∧
      TupleN Δ lam R i k n b z ∧ z.2 (n - 1) = true ∧
      NoBacktracking R (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) i := by
  have hfin : Regeneration.regenerationTime Δ lam R z i k ≠ ⊤ := by
    rw [h]; exact ENNReal.coe_ne_top
  obtain ⟨b, hb⟩ := exists_indices Δ hΔ lam R z i k hfin
  have hb0 : b 0 = 0 := by
    have h0 := hb 0 (Nat.zero_le _)
    have hz : Regeneration.regenerationTime Δ lam R z i 0 = 0 := by
      simp [Regeneration.regenerationTime]
    rw [hz] at h0
    have h1 : ((b 0 : ℝ≥0) * Δ) = 0 := by
      have := ENNReal.coe_eq_zero.mp h0.symm
      exact this
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact_mod_cast h2
    · exact absurd h2 hΔ.ne'
  have hbk : b k = n := by
    have h1 := hb k le_rfl
    rw [h] at h1
    have h2 : ((n : ℝ≥0) * Δ) = (b k : ℝ≥0) * Δ := ENNReal.coe_injective h1
    exact_mod_cast (mul_right_cancel₀ hΔ.ne' h2).symm
  have hcyc : ∀ j < k, b j + 2 ≤ b (j + 1) ∧ CycleOK Δ lam R i z (b j) (b (j + 1)) := by
    intro j hj
    obtain ⟨hsep, hF⟩ := regenerationTime_succ_grid Δ hΔ lam R hlam hR z i j (b j) (b (j + 1))
      (hb j (by omega)) (hb (j + 1) (by omega))
    exact ⟨hsep, (cycle_iff Δ hΔ lam R i hs z (b j) (b (j + 1)) hsep).mp hF⟩
  have hkm : k - 1 + 1 = k := by omega
  have hlast := (hcyc (k - 1) (by omega)).2
  rw [hkm, hbk] at hlast
  refine ⟨b, hb, ⟨hb0, hbk, fun j hj => (hcyc j hj).1, fun j hj => (hcyc j hj).2.1,
    fun j hj hj1 => (hcyc j hj).2.2.1, ?_⟩, hlast.2.1, hlast.2.2⟩
  intro j hj hj1 u hu1 hu2
  have hnb := (Regeneration.noBacktracking_iff_forall R _ i).mp (hcyc j hj).2.2.2
    (u - (b (j + 1) : ℝ≥0) * Δ)
  change -R < z.1 ((b (j + 1) : ℝ≥0) * Δ + (u - (b (j + 1) : ℝ≥0) * Δ)) i -
    z.1 ((b (j + 1) : ℝ≥0) * Δ + 0) i at hnb
  rw [add_tsub_cancel_of_le hu1, add_zero] at hnb
  linarith

theorem unique_of_time {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam)
    (hR : 0 < R) (i : Fin d) (hs : SliceChar Δ lam R i) (z : CoupledSample d)
    (k n : ℕ) (hk : 1 ≤ k)
    (h : Regeneration.regenerationTime Δ lam R z i k = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    ∃! a : Fin (k + 1) → Fin (n + 1),
      z ∈ tupleEventS Δ lam R i k n (fun j => (a j).val) ∧
      ∀ j : Fin (k + 1), Regeneration.regenerationTime Δ lam R z i j.val =
        ((((a j).val : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨b, hb, hT, -, -⟩ := forward_of_time Δ hΔ lam R hlam hR i hs z k n hk h
  have hbn : ∀ m j, j + m = k → b j ≤ n := by
    intro m
    induction m with
    | zero =>
      intro j hj
      have : j = k := by omega
      subst this
      exact hT.2.1.le
    | succ m ih =>
      intro j hj
      have h1 := ih (j + 1) (by omega)
      have h2 := hT.2.2.1 j (by omega)
      omega
  have hbn' : ∀ j ≤ k, b j ≤ n := fun j hj => hbn (k - j) j (by omega)
  refine ⟨fun j => ⟨b j.val, Nat.lt_succ_of_le (hbn' j.val (by have := j.2; omega))⟩,
    ⟨?_, fun j => hb j.val (by have := j.2; omega)⟩, ?_⟩
  · exact (tupleEventS_iff Δ lam R i k n b z).mpr hT
  · rintro a' ⟨-, ha'⟩
    funext j
    apply Fin.ext
    have h1 := ha' j
    rw [hb j.val (by have := j.2; omega)] at h1
    have h2 : (b j.val : ℝ≥0) * Δ = ((a' j).val : ℝ≥0) * Δ := ENNReal.coe_injective h1
    have h3 := mul_right_cancel₀ hΔ.ne' h2
    exact_mod_cast h3.symm

/-! ## The backward direction -/

theorem back_of_tuple {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam)
    (hR : 0 < R) (i : Fin d) (hs : SliceChar Δ lam R i) (z : CoupledSample d)
    (hgain : ∀ m : ℕ, z.2 m = true →
      z.1 ((m : ℝ≥0) * Δ) i + 8 * R ≤ z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) i)
    (hsupp : ∀ m : ℕ, z.2 m = true → ∀ t : ℝ≥0, (m : ℝ≥0) * Δ ≤ t →
      t ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ → z.1 t ∈ couplingRegion i R (z.1 ((m : ℝ≥0) * Δ)))
    (k n : ℕ) (hk : 1 ≤ k) (b : ℕ → ℕ) (hT : TupleN Δ lam R i k n b z)
    (hlast : z.2 (n - 1) = true)
    (hNB : NoBacktracking R (pathTimeShift z.1 ((n : ℝ≥0) * Δ)) i) :
    Regeneration.regenerationTime Δ lam R z i k = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨hb0, hbk, hsep, htrial, hbit, hsurv⟩ := hT
  have hkm : k - 1 + 1 = k := by omega
  have hn2 : 2 ≤ n := by
    have := hsep (k - 1) (by omega)
    rw [hkm, hbk] at this
    omega
  have hheight : ∀ j < k, z.1 ((b j : ℝ≥0) * Δ) i + 2 * R ≤
      z.1 (((b (j + 1) - 1 : ℕ) : ℝ≥0) * Δ) i := by
    intro j hj
    have hg := Regeneration.forcedBitTrialEvent_geometry Δ hΔ lam R hlam hR i
      (b (j + 1) - b j - 1) _ (htrial j hj)
    have h2 := hg.2
    have hidx : b j + (b (j + 1) - b j - 1) = b (j + 1) - 1 := by
      have := hsep j hj; omega
    have e1 : (sampleTimeShift Δ z ((b j : ℝ≥0) * Δ)).1
        (((b (j + 1) - b j - 1 : ℕ) : ℝ≥0) * Δ) i =
        z.1 (((b (j + 1) - 1 : ℕ) : ℝ≥0) * Δ) i := by
      change z.1 ((b j : ℝ≥0) * Δ + ((b (j + 1) - b j - 1 : ℕ) : ℝ≥0) * Δ) i = _
      rw [← add_mul, ← Nat.cast_add, hidx]
    have e0 : (sampleTimeShift Δ z ((b j : ℝ≥0) * Δ)).1 0 i =
        z.1 ((b j : ℝ≥0) * Δ) i := by
      change z.1 ((b j : ℝ≥0) * Δ + 0) i = _
      rw [add_zero]
    rw [e1, e0] at h2
    linarith
  have hjump : ∀ j < k, j + 1 < k →
      z.1 (((b (j + 1) - 1 : ℕ) : ℝ≥0) * Δ) i + 8 * R ≤ z.1 ((b (j + 1) : ℝ≥0) * Δ) i := by
    intro j hj hj1
    have hpos : 1 ≤ b (j + 1) := by have := hsep j hj; omega
    have h1 := hgain (b (j + 1) - 1) (hbit j hj hj1)
    rwa [Nat.sub_add_cancel hpos] at h1
  have hmono : ∀ j, j < k → ∀ j', j' ≤ j →
      z.1 ((b j' : ℝ≥0) * Δ) i ≤ z.1 ((b j : ℝ≥0) * Δ) i := by
    intro j
    induction j with
    | zero =>
      intro _ j' hj'
      have : j' = 0 := by omega
      subst this
      exact le_rfl
    | succ j ih =>
      intro hj j' hj'
      rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
      · have hy := ih (by omega) j' (by omega)
        have h1 := hheight j (by omega)
        have h2 := hjump j (by omega) hj
        linarith
      · have : j' = j + 1 := by omega
        subst this
        exact le_rfl
  have hgeom : ∀ j, j + 1 < k →
      z.1 ((b (j + 1) : ℝ≥0) * Δ) i ≤ z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ) i := by
    intro j hj
    have h1 := hmono (k - 1) (by omega) (j + 1) (by omega)
    have h2 := hheight (k - 1) (by omega)
    rw [hkm, hbk] at h2
    linarith
  have hnn : n - 1 + 1 = n := by omega
  have hcycle : ∀ j < k, CycleOK Δ lam R i z (b j) (b (j + 1)) := by
    intro j hj
    refine ⟨htrial j hj, ?_, ?_⟩
    · by_cases hj1 : j + 1 < k
      · exact hbit j hj hj1
      · have : j + 1 = k := by omega
        rw [this, hbk]
        exact hlast
    · by_cases hj1 : j + 1 < k
      · rw [Regeneration.noBacktracking_iff_forall]
        intro t
        change -R < z.1 ((b (j + 1) : ℝ≥0) * Δ + t) i -
          z.1 ((b (j + 1) : ℝ≥0) * Δ + 0) i
        rw [add_zero]
        have hY := hgeom j hj1
        by_cases hu1 : (b (j + 1) : ℝ≥0) * Δ + t ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ
        · have := hsurv j hj hj1 ((b (j + 1) : ℝ≥0) * Δ + t)
            (le_add_of_nonneg_right zero_le) hu1
          linarith
        · have hu1' : ((n - 1 : ℕ) : ℝ≥0) * Δ < (b (j + 1) : ℝ≥0) * Δ + t := lt_of_not_ge hu1
          by_cases hu2 : (b (j + 1) : ℝ≥0) * Δ + t ≤ (n : ℝ≥0) * Δ
          · have hreg := hsupp (n - 1) hlast ((b (j + 1) : ℝ≥0) * Δ + t) hu1'.le
              (by rw [hnn]; exact hu2)
            have hbd := (Regeneration.couplingRegion_coordinate_bounds i R _ _ hreg).1
            linarith
          · have hu2' : (n : ℝ≥0) * Δ ≤ (b (j + 1) : ℝ≥0) * Δ + t := (lt_of_not_ge hu2).le
            have hnb := (Regeneration.noBacktracking_iff_forall R _ i).mp hNB
              ((b (j + 1) : ℝ≥0) * Δ + t - (n : ℝ≥0) * Δ)
            change -R < z.1 ((n : ℝ≥0) * Δ + ((b (j + 1) : ℝ≥0) * Δ + t - (n : ℝ≥0) * Δ)) i -
              z.1 ((n : ℝ≥0) * Δ + 0) i at hnb
            rw [add_tsub_cancel_of_le hu2', add_zero] at hnb
            have hg := hgain (n - 1) hlast
            rw [hnn] at hg
            linarith
      · have : j + 1 = k := by omega
        rw [this, hbk]
        exact hNB
  have hτ : ∀ j ≤ k, Regeneration.regenerationTime Δ lam R z i j =
      (((b j : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [Regeneration.regenerationTime, hb0]
    | succ j ih =>
      intro hj
      have hsp := hsep j (by omega)
      have hcy := (cycle_iff Δ hΔ lam R i hs z (b j) (b (j + 1)) hsp).mpr
        (hcycle j (by omega))
      exact regenerationTime_succ_of_first Δ lam R z i j (b j) (b (j + 1))
        (ih (by omega)) (by omega) hcy
  have hfinal := hτ k le_rfl
  rw [hbk] at hfinal
  exact hfinal

/-! ## Almost-sure facts of the actual coupling -/

private theorem successful_endpoint_gain' {d : ℕ} (Δ : ℝ≥0) (R δ : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (xω : Vec d × FieldPair d)
    (hone : Regeneration.Renewal.OneIntervalKernelAt Δ δ R i P K xω)
    (hstart : ∀ x : Vec d, ∀ᵐ γ ∂P (x, xω.2), γ 0 = x) :
    ∀ᵐ z ∂K xω, ∀ n : ℕ, z.2 n = true →
      z.1 ((n : ℝ≥0) * Δ) i + 8 * R ≤ z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ) i := by
  classical
  apply ae_all_iff.mpr
  intro n
  let F : Path d → ℝ := fun γ => if γ Δ i < γ 0 i + 8 * R then 1 else 0
  have hF : Measurable F := Measurable.ite
    (measurableSet_lt ((measurable_pi_apply i).comp (continuous_eval_const Δ).measurable)
      (((measurable_pi_apply i).comp (continuous_eval_const 0).measurable).add_const _))
    measurable_const measurable_const
  have hbF : Regeneration.BoundedRealTest F := ⟨1, fun γ => by
    dsimp only [F]; split_ifs <;> norm_num⟩
  have hseg : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ' := by
    intro γ γ' h
    dsimp only [F]
    rw [h Δ le_rfl, h 0 zero_le]
  have hzero (x : Vec d) :
      (∫ γ, F γ ∂Regeneration.Renewal.killedBridgeMixture Δ R i P x xω.2) = 0 := by
    have hs : ∀ᵐ γ ∂Regeneration.Renewal.killedBridgeMixture Δ R i P x xω.2, γ 0 = x :=
      (withDensity_absolutelyContinuous _ _).ae_le
        (ae_restrict_of_ae (hstart x))
    apply integral_eq_zero_of_ae
    filter_upwards [hs, Regeneration.ae_killedBridgeMixture_endpoint_mem Δ R i P x xω.2]
      with γ hγ hb
    change F γ = 0
    have hg := (Regeneration.endpointBall_coordinate_bounds i R x (γ Δ) hb).1
    simp only [F, hγ, not_lt.mpr hg.le, ↓reduceIte]
  obtain ⟨hint, _, heq, _⟩ := hone n (fun _ => 1) F measurable_const
    ⟨1, fun _ => by norm_num⟩ hF hbF hseg
  simp_rw [hzero] at heq
  simp only [mul_zero, integral_zero] at heq
  have hnneg : ∀ z : Regeneration.CoupledSample d,
      0 ≤ (1 : ℝ) * (if z.2 n = true then 1 else 0) *
        F (Regeneration.pathTimeShift z.1 ((n : ℝ≥0) * Δ)) := by
    intro z
    dsimp only [F]
    split_ifs <;> norm_num
  have haz := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnneg) hint).mp heq
  filter_upwards [haz] with z hz
  intro hb
  simp only [hb, ↓reduceIte, one_mul] at hz
  have ht : (n : ℝ≥0) * Δ + Δ = ((n + 1 : ℕ) : ℝ≥0) * Δ := by
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  change (if z.1 ((n : ℝ≥0) * Δ + Δ) i <
    z.1 ((n : ℝ≥0) * Δ + 0) i + 8 * R then (1 : ℝ) else 0) = 0 at hz
  rw [ht, add_zero] at hz
  split_ifs at hz with h
  · norm_num at hz
  · exact le_of_not_gt h

/-- A measurable event containing every `(ω, z)` whose path/coin sample satisfies the
successful-interval facts holds almost surely. -/
theorem ae_mem_of_facts {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (M : Set (FieldPair d × CoupledSample d)) (hM : MeasurableSet M)
    (hback : ∀ z : CoupledSample d,
      (∀ m : ℕ, z.2 m = true →
        z.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam) (Regeneration.Renewal.forceCoord hd)
          + 8 * (l / lam) ≤
        z.1 (((m + 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)
          (Regeneration.Renewal.forceCoord hd)) →
      (∀ m : ℕ, z.2 m = true → ∀ t : ℝ≥0,
        (m : ℝ≥0) * Regeneration.Renewal.regenDelta lam ≤ t →
        t ≤ ((m + 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam →
        z.1 t ∈ couplingRegion (Regeneration.Renewal.forceCoord hd) (l / lam)
          (z.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam))) →
      ∀ ω : FieldPair d, (ω, z) ∈ M) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, q ∈ M := by
  apply Measure.ae_compProd_of_ae_ae hM
  filter_upwards [hK.1.1, hK.2.2.1, hK.2.2.2.2.2.1.1, hK.2.2.2.2.2.2.2.1]
    with ω hp hP hb hone
  haveI : IsProbabilityMeasure (Regeneration.originCoupledLaw K ω) := hp
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (Regeneration.originCoupledLaw K) ω]
  obtain ⟨_, r, hr⟩ := hP
  have hs : ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x := by
    intro x
    rw [hr x]
    exact r.pathLaw_starts_at x
  have he := successful_endpoint_gain' (Regeneration.Renewal.regenDelta lam) (l / lam) δ
    (Regeneration.Renewal.forceCoord hd) P K (0, ω) hone hs
  filter_upwards [hb, he] with z hz hgain
  exact hback z hgain hz ω

/-! ## The node -/

theorem node_rt_u3A_prebridge_u2D_k_of_deps
    (hslices : node_app_u3A_factorization_u23_slicesStmt) :
    node_rt_u3A_prebridge_u2D_kStmt := by
  intro d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  dsimp only
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  have hs : SliceChar (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) := by
    intro m hm z
    have h := (hslices d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK m hm).2.1 z
    have ht : regenerationTime hd lam l 1 z =
        firstRegenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) z
          (Regeneration.Renewal.forceCoord hd) :=
      Regeneration.regenerationTime_one _ _ _ _ _
    rw [ht] at h
    exact h
  intro k n hk hn
  have hΓ := measurableSet_tupleUnionS (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) hR
    (Regeneration.Renewal.forceCoord hd) k n
  refine ⟨hΓ, ?_⟩
  have hΓg : MeasurableSet {q : FieldPair d × CoupledSample d | q.2 ∈
      tupleUnionS (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n} :=
    ((Probability.finiteHistorySigma_le (d := d) (Regeneration.Renewal.regenDelta lam) (n - 1))
      _ hΓ).preimage measurable_snd
  have hcoin : MeasurableSet {q : FieldPair d × CoupledSample d | q.2.2 (n - 1) = true} :=
    measurableSet_eq_fun ((measurable_pi_apply (n - 1)).comp measurable_snd.snd) measurable_const
  have hshift : Measurable (fun q : FieldPair d × CoupledSample d =>
      pathTimeShift q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) :=
    Probability.continuous_path_time_shift.measurable.comp
      (measurable_const.prodMk measurable_snd.fst)
  have hNBm : MeasurableSet {q : FieldPair d × CoupledSample d |
      NoBacktracking (l / lam)
        (pathTimeShift q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        (Regeneration.Renewal.forceCoord hd)} :=
    (Regeneration.measurableSet_NoBacktracking (l / lam) (Regeneration.Renewal.forceCoord hd)).preimage
      hshift
  have htime : MeasurableSet {q : FieldPair d × CoupledSample d |
      Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) q.2
        (Regeneration.Renewal.forceCoord hd) k =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} :=
    measurableSet_eq_fun
      ((Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
        (l / lam) (Regeneration.Renewal.forceCoord hd) k).comp measurable_snd)
      measurable_const
  let M : Set (FieldPair d × CoupledSample d) := {q | (q.2 ∈
      tupleUnionS (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n ∧ q.2.2 (n - 1) = true ∧
      NoBacktracking (l / lam)
        (pathTimeShift q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        (Regeneration.Renewal.forceCoord hd)) →
      Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) q.2
        (Regeneration.Renewal.forceCoord hd) k =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hM : MeasurableSet M := MeasurableSet.imp (hΓg.inter (hcoin.inter hNBm)) htime
  have hae : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, q ∈ M := by
    refine ae_mem_of_facts hd Q lam h₀ h₁ l δ P K hK M hM ?_
    intro z hgain hsupp ω hz
    obtain ⟨hmem, hlast, hNB⟩ := hz
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hmem
    let b : ℕ → ℕ := fun j => if h : j < k + 1 then ((a ⟨j, h⟩ : Fin (n + 1)) : ℕ) else 0
    have hfun : (fun j : Fin (k + 1) => (a j).val) = fun j : Fin (k + 1) => b j.val := by
      funext j
      have hj : j.val < k + 1 := j.isLt
      simp only [b, hj, ↓reduceDIte]
      try rfl
    rw [hfun] at ha
    exact back_of_tuple (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) h₀ hR
      (Regeneration.Renewal.forceCoord hd) hs z hgain hsupp k n hk b
      ((tupleEventS_iff _ lam (l / lam) _ k n b z).mp ha) hlast hNB
  filter_upwards [hae] with q hq
  have hfwd : Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) q.2
      (Regeneration.Renewal.forceCoord hd) k =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) →
      (q.2 ∈ tupleUnionS (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n ∧ q.2.2 (n - 1) = true ∧
      NoBacktracking (l / lam)
        (pathTimeShift q.2.1 ((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        (Regeneration.Renewal.forceCoord hd)) := by
    intro h
    obtain ⟨b, -, hT, hlast, hNB⟩ := forward_of_time (Regeneration.Renewal.regenDelta lam) hΔ lam
      (l / lam) h₀ hR (Regeneration.Renewal.forceCoord hd) hs q.2 k n hk h
    refine ⟨?_, hlast, hNB⟩
    have hbn : ∀ m j, j + m = k → b j ≤ n := by
      intro m
      induction m with
      | zero =>
        intro j hj
        have : j = k := by omega
        subst this
        exact hT.2.1.le
      | succ m ih =>
        intro j hj
        have h1 := ih (j + 1) (by omega)
        have h2 := hT.2.2.1 j (by omega)
        omega
    have hbn' : ∀ j ≤ k, b j ≤ n := fun j hj => hbn (k - j) j (by omega)
    refine Set.mem_iUnion.mpr ⟨fun j => ⟨b j.val, Nat.lt_succ_of_le
      (hbn' j.val (by have := j.2; omega))⟩, ?_⟩
    exact (tupleEventS_iff _ lam (l / lam) _ k n b q.2).mpr hT
  refine ⟨⟨hfwd, hq⟩, fun h1 h2 h3 => ?_⟩
  exact unique_of_time (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) h₀ hR
    (Regeneration.Renewal.forceCoord hd) hs q.2 k n hk (hq ⟨h1, h2, h3⟩)

end EinsteinFull.Blueprint
