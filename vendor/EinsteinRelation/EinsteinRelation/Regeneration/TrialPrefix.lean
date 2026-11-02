import EinsteinRelation.Regeneration.CandidatePrefix
import EinsteinRelation.Regeneration.RegenerationGrid

/-! # Nonanticipativity of the trial starts

Source `paper/main.tex:305–318,353–364`. A full trial start is selected one grid
interval after its successful candidate. Its selection therefore uses the path and
the candidate bits only through that preceding grid time.
-/

open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

private theorem hittingBelow_eq_of_prefix {d : ℕ} (γ γ' : Path d) (i : Fin d)
    (a : ℝ) (T : ℝ≥0) (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, γ t = γ' t)
    (hle : firstHittingBelow γ i a ≤ (T : ℝ≥0∞)) :
    firstHittingBelow γ i a = firstHittingBelow γ' i a := by
  have h0 := hpre 0 ⟨le_rfl, zero_le⟩
  have hle' : firstHittingBelow γ' i a ≤ (T : ℝ≥0∞) := by
    obtain ⟨t, ht, hcross⟩ := (Probability.downcrossing_inf_le_iff γ i a T).mp hle
    apply (Probability.downcrossing_inf_le_iff γ' i a T).mpr
    exact ⟨t, ht, by rwa [← hpre t ht, ← h0]⟩
  have hbound : ∀ (f g : Path d),
      (∀ t ∈ Set.Icc (0 : ℝ≥0) T, f t = g t) →
      firstHittingBelow f i a ≤ (T : ℝ≥0∞) →
      firstHittingBelow f i a ≤ firstHittingBelow g i a := by
    intro f g hp hlefg
    refine le_iInf fun t => le_iInf fun ht => ?_
    by_cases htT : t ≤ T
    · apply firstHittingBelow_le_of_crossing
      rwa [hp t ⟨zero_le, htT⟩, hp 0 ⟨le_rfl, zero_le⟩]
    · exact hlefg.trans (ENNReal.coe_le_coe.mpr (le_of_lt (not_le.mp htT)))
  exact le_antisymm (hbound γ γ' hpre hle)
    (hbound γ' γ (fun t ht => (hpre t ht).symm) hle')

private theorem shifted_prefix {d : ℕ} (z z' : CoupledSample d) (T t : ℝ≥0)
    (ht : t ≤ T) (hpre : ∀ s ∈ Set.Icc (0 : ℝ≥0) T, z.1 s = z'.1 s) :
    ∀ s ∈ Set.Icc (0 : ℝ≥0) (T - t),
      (pathTimeShift z.1 t) s = (pathTimeShift z'.1 t) s := by
  intro s hs
  exact hpre (t + s) ⟨zero_le, by
    calc t + s ≤ t + (T - t) := add_le_add le_rfl hs.2
      _ = T := add_tsub_cancel_of_le ht⟩

private theorem shifted_bits {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (z z' : CoupledSample d) (T t : ℝ≥0) (ht : t ≤ T)
    (hgrid : ∃ k : ℕ, t = (k : ℝ≥0) * Δ)
    (hbits : ∀ k : ℕ, (k : ℝ≥0) * Δ ≤ T → z.2 k = z'.2 k) :
    ∀ k : ℕ, (k : ℝ≥0) * Δ ≤ T - t →
      (sampleTimeShift Δ z t).2 k = (sampleTimeShift Δ z' t).2 k := by
  obtain ⟨j, rfl⟩ := hgrid
  intro k hk
  change z.2 (gridIndex Δ ((j : ℝ≥0) * Δ) + k) =
    z'.2 (gridIndex Δ ((j : ℝ≥0) * Δ) + k)
  rw [gridIndex_mul Δ hΔ]
  apply hbits
  rw [Nat.cast_add, add_mul]
  exact (add_le_add le_rfl hk).trans (add_tsub_cancel_of_le ht).le

private theorem add_coe_tsub (S : ℝ≥0∞) (T : ℝ≥0) (hS : S ≠ ⊤)
    (hST : S.toNNReal ≤ T) : S + ((T - S.toNNReal : ℝ≥0) : ℝ≥0∞) = (T : ℝ≥0∞) := by
  calc S + ((T - S.toNNReal : ℝ≥0) : ℝ≥0∞) =
        (S.toNNReal : ℝ≥0∞) + ((T - S.toNNReal : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_toNNReal hS]
    _ = (T : ℝ≥0∞) := by rw [← ENNReal.coe_add, add_tsub_cancel_of_le hST]

private theorem failure_eq_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R : ℝ) (z z' : CoupledSample d) (i : Fin d) (T : ℝ≥0) (S : ℝ≥0∞)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, z.1 t = z'.1 t)
    (hle : trialFailureTime Δ R z i S ≤ (T : ℝ≥0∞)) :
    trialFailureTime Δ R z i S = trialFailureTime Δ R z' i S := by
  have hdown : trialDownwardTime Δ R z i S ≤ (T : ℝ≥0∞) :=
    (le_roundUp Δ hΔ _).trans hle
  have hS : S ≠ ⊤ := by
    intro ht
    rw [trialDownwardTime, if_pos ht] at hdown
    exact (not_le_of_gt ENNReal.coe_lt_top) hdown
  rw [trialDownwardTime, if_neg hS] at hdown
  have hST : S ≤ (T : ℝ≥0∞) := (le_add_right le_rfl).trans hdown
  have hST' : S.toNNReal ≤ T := ENNReal.coe_le_coe.mp (by
    rwa [ENNReal.coe_toNNReal hS])
  have hhit : firstHittingBelow (pathTimeShift z.1 S.toNNReal) i (-R) ≤
      ((T - S.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    apply (ENNReal.add_le_add_iff_left (a := S) hS).mp
    rw [add_coe_tsub S T hS hST']
    exact hdown
  have heq := hittingBelow_eq_of_prefix (pathTimeShift z.1 S.toNNReal)
    (pathTimeShift z'.1 S.toNNReal) i (-R) (T - S.toNNReal)
    (shifted_prefix z z' T S.toNNReal hST' hpre) hhit
  simp only [trialFailureTime, trialDownwardTime, if_neg hS, sampleTimeShift, heq]

private theorem maximum_eq_of_prefix {d : ℕ} (z z' : CoupledSample d) (i : Fin d)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hpre : ∀ s ∈ Set.Icc (0 : ℝ≥0) T, z.1 s = z'.1 s) :
    coordinateMaximum z.1 i t = coordinateMaximum z'.1 i t := by
  unfold coordinateMaximum
  congr 1
  apply Set.image_congr
  intro s hs
  rw [hpre s ⟨hs.1, hs.2.trans ht⟩, hpre 0 ⟨le_rfl, zero_le⟩]

/-- A trial start through `T + Δ` is determined by the path through `T` and the bits
at grid times at most `T` (`paper/main.tex:305–318,353–364`). -/
theorem trialStartSequence_eq_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hR : 0 < R) (z z' : CoupledSample d) (i : Fin d) (n : ℕ)
    (T : ℝ≥0) (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, z.1 t = z'.1 t)
    (hbits : ∀ k : ℕ, (k : ℝ≥0) * Δ ≤ T → z.2 k = z'.2 k)
    (hle : trialStartSequence Δ lam R z i n ≤ ((T + Δ : ℝ≥0) : ℝ≥0∞)) :
    trialStartSequence Δ lam R z i n = trialStartSequence Δ lam R z' i n := by
  induction n with
  | zero =>
    rw [trialStartSequence, ENNReal.coe_add] at hle
    have hN := (ENNReal.add_le_add_iff_right (a := (Δ : ℝ≥0∞)) ENNReal.coe_ne_top).mp hle
    have heq := firstSuccessfulCandidate_eq_of_prefix Δ hΔ lam R (3 * lam * R) hR
      z z' i T hpre hbits hN
    simp only [trialStartSequence, heq]
  | succ n ih =>
    let t := trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n)
    have ht : t ≠ ⊤ := by
      intro ht
      rw [trialStartSequence, if_pos ht] at hle
      exact (not_le_of_gt ENNReal.coe_lt_top) hle
    let a := lam * (coordinateMaximum z.1 i t.toNNReal -
      (z.1 t.toNNReal i - z.1 0 i) + R)
    have hform : trialStartSequence Δ lam R z i (n + 1) =
        t + firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i + Δ := by
      rw [trialStartSequence, if_neg ht]
    rw [hform, ENNReal.coe_add] at hle
    have hTN := (ENNReal.add_le_add_iff_right (a := (Δ : ℝ≥0∞)) ENNReal.coe_ne_top).mp hle
    have htT : t ≤ (T : ℝ≥0∞) := (le_add_right le_rfl).trans hTN
    have htT' : t.toNNReal ≤ T := ENNReal.coe_le_coe.mp (by
      rwa [ENNReal.coe_toNNReal ht])
    have hS : trialStartSequence Δ lam R z i n ≠ ⊤ := by
      intro hS
      apply ht
      simp only [t, trialFailureTime, trialDownwardTime, if_pos hS, roundUp, if_true]
    have hSt : trialStartSequence Δ lam R z i n ≤ t := by
      apply le_trans _ (le_roundUp Δ hΔ _)
      rw [trialDownwardTime, if_neg hS]
      exact le_add_right le_rfl
    have hprevEq := ih ((hSt.trans htT).trans (by
      rw [ENNReal.coe_add]
      exact le_add_right le_rfl))
    have hteq : t = trialFailureTime Δ R z' i (trialStartSequence Δ lam R z' i n) := by
      rw [← hprevEq]
      exact failure_eq_of_prefix Δ hΔ R z z' i T _ hpre htT
    have ht' : trialFailureTime Δ R z' i (trialStartSequence Δ lam R z' i n) ≠ ⊤ :=
      hteq ▸ ht
    have hstep : firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i ≤
        ((T - t.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      apply (ENNReal.add_le_add_iff_left (a := t) ht).mp
      rw [add_coe_tsub t T ht htT']
      exact hTN
    obtain ⟨j, hj⟩ := trialFailureTime_mem_grid Δ R z i
      (trialStartSequence Δ lam R z i n) ht
    have hj' : t.toNNReal = (j : ℝ≥0) * Δ := by
      change (trialFailureTime Δ R z i _).toNNReal = _
      rw [hj, ENNReal.toNNReal_coe]
    have hstepEq := firstSuccessfulCandidate_eq_of_prefix Δ hΔ lam R a hR
      (sampleTimeShift Δ z t.toNNReal) (sampleTimeShift Δ z' t.toNNReal) i (T - t.toNNReal)
      (shifted_prefix z z' T t.toNNReal htT' hpre)
      (shifted_bits Δ hΔ z z' T t.toNNReal htT' ⟨j, hj'⟩ hbits) hstep
    have hmax := maximum_eq_of_prefix z z' i T t.toNNReal htT' hpre
    have hat : a = lam * (coordinateMaximum z'.1 i t.toNNReal -
        (z'.1 t.toNNReal i - z'.1 0 i) + R) := by
      dsimp only [a]
      rw [hmax, hpre t.toNNReal ⟨zero_le, htT'⟩, hpre 0 ⟨le_rfl, zero_le⟩]
    rw [hform, trialStartSequence, if_neg ht', ← hteq, ← hat]
    change t + firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i + Δ =
      t + firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z' t.toNNReal) i + Δ
    rw [hstepEq]


end EinsteinRelation.Regeneration
