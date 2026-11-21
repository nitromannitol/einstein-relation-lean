import EinsteinFull.Regeneration.TrialStepIdentity

/-!
# Trial starts and failures are decided by the observed history

Every finite trial start is preceded by a successful coin and its bridge, so the
running maximum at a trial start exceeds the displacement there by at most `12R`.
The trial starts and the failure times, together with the heights and search levels
attached to them, are decided by the observed history at those times.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence
  firstSuccessfulCandidate

/-- The running maximum at a finite trial start exceeds the displacement there by at most
`12R`, under the support property of the successful bridges. -/
theorem trialStart_maximum_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam)
    (hR : 0 < R) (z : CoupledSample d) (i : Fin d) (n : ℕ)
    (hbridge : ∀ k : ℕ, z.2 k = true → ∀ t : ℝ≥0,
      (k : ℝ≥0) * Δ ≤ t → t ≤ ((k + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ couplingRegion i R (z.1 ((k : ℝ≥0) * Δ)))
    (hS : trialStartSequence Δ lam R z i n ≠ ⊤) :
    coordinateMaximum z.1 i (trialStartSequence Δ lam R z i n).toNNReal ≤
      z.1 (trialStartSequence Δ lam R z i n).toNNReal i - z.1 0 i + 12 * R := by
  obtain ⟨k, hk⟩ := trialStartSequence_mem_grid Δ hΔ lam R z i n hS
  have htwo := two_step_le_trialStartSequence Δ hΔ lam R hlam hR z i n
  have hk2 : 2 ≤ k := by
    rw [hk] at htwo
    have h : (2 : ℝ≥0) * Δ ≤ (k : ℝ≥0) * Δ := by exact_mod_cast htwo
    exact_mod_cast le_of_mul_le_mul_right h hΔ
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hbit := trialStartSequence_last_bit Δ hΔ lam R z i n m hk
  have hStime : (trialStartSequence Δ lam R z i n).toNNReal = ((m + 1 : ℕ) : ℝ≥0) * Δ := by
    rw [hk, ENNReal.toNNReal_coe]
  have hpre : (trialStartSequence Δ lam R z i n).toNNReal - Δ = (m : ℝ≥0) * Δ := by
    rw [hStime]
    push_cast
    rw [add_mul, one_mul, add_tsub_cancel_right]
  have hslack := trial_prestart_maximum_slack Δ hΔ lam R hlam hR z i n hS
  rw [hpre] at hslack
  have hregion : ∀ t : ℝ≥0, (m : ℝ≥0) * Δ ≤ t → t ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ →
      z.1 t i < z.1 ((m : ℝ≥0) * Δ) i + 11 * R ∧ z.1 ((m : ℝ≥0) * Δ) i - R < z.1 t i := by
    intro t ht1 ht2
    have h := couplingRegion_coordinate_bounds i R _ _ (hbridge m hbit t ht1 ht2)
    exact ⟨h.2, h.1⟩
  have hsplit : ((m + 1 : ℕ) : ℝ≥0) * Δ = (m : ℝ≥0) * Δ + Δ := by
    push_cast
    ring
  have hend := (hregion (((m + 1 : ℕ) : ℝ≥0) * Δ)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ m) zero_le) le_rfl).2
  rw [hStime, hsplit, coordinateMaximum_add]
  apply max_le
  · rw [← hsplit]
    linarith
  · have hwin : coordinateMaximum (pathTimeShift z.1 ((m : ℝ≥0) * Δ)) i Δ ≤ 11 * R := by
      apply coordinateMaximum_le
      intro s hs
      have h := (hregion ((m : ℝ≥0) * Δ + s) (le_add_of_nonneg_right zero_le)
        (by rw [hsplit]; exact add_le_add le_rfl hs.2)).1
      change z.1 ((m : ℝ≥0) * Δ + s) i - z.1 ((m : ℝ≥0) * Δ + 0) i ≤ 11 * R
      rw [add_zero]
      linarith
    rw [← hsplit]
    linarith

/-- Trial starts and their heights are decided by the observed history. -/
theorem trialStart_historyDecided {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam)
    (hR : 0 < R) (i : Fin d) (n : ℕ) :
    HistoryDecided Δ (fun z => trialStartSequence Δ lam R z i n)
      (fun z => z.1 (trialStartSequence Δ lam R z i n).toNNReal - z.1 0) := by
  intro m z z' hag hS0
  have hS : trialStartSequence Δ lam R z i n = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hS0
  have htwo := two_step_le_trialStartSequence Δ hΔ lam R hlam hR z i n
  have hm : 1 ≤ m := by
    rw [hS] at htwo
    have h : (2 : ℝ≥0) * Δ ≤ (m : ℝ≥0) * Δ := by exact_mod_cast htwo
    have h2 : (2 : ℝ≥0) ≤ m := le_of_mul_le_mul_right h hΔ
    have h3 : (2 : ℕ) ≤ m := by exact_mod_cast h2
    omega
  have hT : ((m - 1 : ℕ) : ℝ≥0) * Δ + Δ = (m : ℝ≥0) * Δ := by
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  have hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) (((m - 1 : ℕ) : ℝ≥0) * Δ), z.1 t = z'.1 t := by
    intro t ht
    apply hag.1
    rw [← hT]
    exact ht.2.trans (le_add_of_nonneg_right zero_le)
  have hbits : ∀ k : ℕ, (k : ℝ≥0) * Δ ≤ ((m - 1 : ℕ) : ℝ≥0) * Δ → z.2 k = z'.2 k := by
    intro k hk
    have hk' : k ≤ m - 1 := by exact_mod_cast le_of_mul_le_mul_right hk hΔ
    exact hag.2 k (by omega)
  have hle : trialStartSequence Δ lam R z i n ≤ (((((m - 1 : ℕ) : ℝ≥0) * Δ + Δ : ℝ≥0)) : ℝ≥0∞) := by
    rw [hT, hS]
  have heq := trialStartSequence_eq_of_prefix Δ hΔ lam R hR z z' i n _ hpre hbits hle
  refine ⟨heq.symm, ?_⟩
  have hSle : (trialStartSequence Δ lam R z i n).toNNReal ≤ (m : ℝ≥0) * Δ := by
    rw [hS, ENNReal.toNNReal_coe]
  change z'.1 (trialStartSequence Δ lam R z' i n).toNNReal - z'.1 0 =
    z.1 (trialStartSequence Δ lam R z i n).toNNReal - z.1 0
  rw [← heq, ← hag.1 _ hSle, ← hag.1 0 zero_le]


/-- Failure times, failure heights and search levels are decided by the observed
history at the failure. -/
theorem trialFailure_historyDecided {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (i : Fin d) (n : ℕ) :
    HistoryDecided Δ (trialFailure Δ lam R i n)
      (fun z => (trialFailureHeight Δ lam R a i n z, trialLevel Δ lam R i n z)) := by
  intro m z z' hag hF0
  have hF : trialFailure Δ lam R i n z = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hF0
  set S := trialStartSequence Δ lam R z i n with hSdef
  have hFne : trialFailure Δ lam R i n z ≠ ⊤ := by rw [hF]; exact ENNReal.coe_ne_top
  have hS : S ≠ ⊤ := by
    intro hS
    apply hFne
    simp only [trialFailure, trialFailureTime, trialDownwardTime, ← hSdef, hS, ite_true]
    simp [roundUp]
  set H := firstHittingBelow (sampleTimeShift Δ z S.toNNReal).1 i (-R) with hHdef
  have hdown : trialDownwardTime Δ R z i S = S + H := by
    simp only [trialDownwardTime, ite_eq_right hS, hHdef]
  have hSH_le : S + H ≤ (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
    rw [← hF, ← hdown]
    exact le_roundUp Δ hΔ _
  have hSle : S ≤ (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := (le_add_right le_rfl).trans hSH_le
  obtain ⟨k, hk⟩ := trialStartSequence_mem_grid Δ hΔ lam R z i n hS
  have hk' : S = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hk
  have hkm : k ≤ m := by
    rw [hk'] at hSle
    have h : (k : ℝ≥0) * Δ ≤ (m : ℝ≥0) * Δ := ENNReal.coe_le_coe.mp hSle
    exact_mod_cast le_of_mul_le_mul_right h hΔ
  have htwo := two_step_le_trialStartSequence Δ hΔ lam R hlam hR z i n
  have hk2 : 2 ≤ k := by
    rw [← hSdef, hk'] at htwo
    have h : (2 : ℝ≥0) * Δ ≤ (k : ℝ≥0) * Δ := by exact_mod_cast htwo
    exact_mod_cast le_of_mul_le_mul_right h hΔ
  -- the trial start is the same for z'
  have hSeq : trialStartSequence Δ lam R z' i n = S := by
    have hdec := trialStart_historyDecided Δ hΔ lam R hlam hR i n k z z' (hag.mono hkm) hk'
    exact hdec.1
  -- the fall is the same
  have hagw := hag.shift hΔ hkm
  have hSnn : S.toNNReal = (k : ℝ≥0) * Δ := by rw [hk', ENNReal.toNNReal_coe]
  have hHle : H ≤ ((((m - k : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
    have hsplit : (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) =
        (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) + ((((m - k : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_add, ← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hkm]
    rw [hsplit, ← hk'] at hSH_le
    exact (ENNReal.add_le_add_iff_left hS).mp hSH_le
  have hHeq : firstHittingBelow (sampleTimeShift Δ z' S.toNNReal).1 i (-R) = H := by
    rw [hSnn]
    rw [hSnn] at hHdef
    rw [hHdef]
    exact firstHittingBelow_eq_of_agree _ _ i (-R) _ (fun t ht => hagw.1 t ht) (hHdef ▸ hHle)
  have hdown' : trialDownwardTime Δ R z' i S = trialDownwardTime Δ R z i S := by
    rw [hdown]
    simp only [trialDownwardTime, ite_eq_right hS]
    rw [hHeq]
  have hFeq : trialFailure Δ lam R i n z' = trialFailure Δ lam R i n z := by
    simp only [trialFailure, trialFailureTime]
    rw [hSeq, hdown']
  refine ⟨hFeq, ?_⟩
  have hFle : (trialFailure Δ lam R i n z).toNNReal ≤ (m : ℝ≥0) * Δ := by
    rw [hF, ENNReal.toNNReal_coe]
  have hmax : coordinateMaximum z'.1 i (trialFailure Δ lam R i n z).toNNReal =
      coordinateMaximum z.1 i (trialFailure Δ lam R i n z).toNNReal := by
    unfold coordinateMaximum
    congr 1
    apply Set.image_congr
    intro s hs
    rw [← hag.1 s (hs.2.trans hFle), ← hag.1 0 zero_le]
  have hval : z'.1 (trialFailure Δ lam R i n z).toNNReal i - z'.1 0 i =
      z.1 (trialFailure Δ lam R i n z).toNNReal i - z.1 0 i := by
    rw [← hag.1 _ hFle, ← hag.1 0 zero_le]
  simp only [Prod.mk.injEq]
  constructor
  · simp only [trialFailureHeight]
    rw [Set.indicator_of_mem (show z' ∈ {z : CoupledSample d | trialFailure Δ lam R i n z ≠ ⊤} by
        change trialFailure Δ lam R i n z' ≠ ⊤
        rw [hFeq]
        exact hFne),
      Set.indicator_of_mem (show z ∈ {z : CoupledSample d | trialFailure Δ lam R i n z ≠ ⊤}
        from hFne), hFeq, hmax]
  · simp only [trialLevel]
    rw [hFeq, hmax, hval]

end EinsteinFull.Regeneration
