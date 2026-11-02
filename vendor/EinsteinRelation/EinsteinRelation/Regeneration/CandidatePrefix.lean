import EinsteinRelation.Regeneration.PassagePrefix
import EinsteinRelation.Regeneration.CandidateGrid

/-! # Nonanticipativity of the rounded candidates

Source `paper/main.tex:283–300,353–364`. The passage-prefix identity extends to the
first good rounded passage and its iterates. Only the closed path window through the
candidate time is used.
-/

open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

private theorem goodPassage_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (γ γ' : Path d) (i : Fin d) (T : ℝ≥0)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, γ t = γ' t) (n : ℕ)
    (hn : IsGoodPassage Δ lam R a γ i n)
    (hu : roundUp Δ (passageSequence Δ lam R a γ i n) ≤ (T : ℝ≥0∞)) :
    IsGoodPassage Δ lam R a γ' i n ∧
      roundUp Δ (passageSequence Δ lam R a γ' i n) =
        roundUp Δ (passageSequence Δ lam R a γ i n) := by
  have hv := (le_roundUp Δ hΔ _).trans hu
  have heq := (passageSequence_prefix_determined Δ hΔ lam R a hR γ γ' i n T hpre).2 hv
  refine ⟨?_, congrArg (roundUp Δ) heq.symm⟩
  unfold IsGoodPassage at hn ⊢
  rw [← heq]
  refine ⟨hn.1, hn.2.1, fun s hs => ?_⟩
  have huT : (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal ≤ T := by
    exact ENNReal.coe_le_coe.mp (by rwa [ENNReal.coe_toNNReal hn.2.1])
  have hvT : (passageSequence Δ lam R a γ i n).toNNReal ≤ T := by
    exact ENNReal.coe_le_coe.mp (by rwa [ENNReal.coe_toNNReal hn.1])
  rw [← hpre s ⟨zero_le, hs.2.trans huT⟩,
    ← hpre _ ⟨zero_le, hvT⟩]
  exact hn.2.2 s hs

/-- The first good rounded passage is determined by the path through its time
(`paper/main.tex:289–294`). -/
theorem firstRoundedCandidate_eq_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (γ γ' : Path d) (i : Fin d) (T : ℝ≥0)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, γ t = γ' t)
    (hle : firstRoundedCandidate Δ lam R a γ i ≤ (T : ℝ≥0∞)) :
    firstRoundedCandidate Δ lam R a γ i = firstRoundedCandidate Δ lam R a γ' i := by
  have hfin : firstRoundedCandidate Δ lam R a γ i ≠ ⊤ := ne_top_of_le_ne_top
    ENNReal.coe_ne_top hle
  have hex : ∃ n, IsGoodPassage Δ lam R a γ i n := by
    by_contra h
    apply hfin
    simp only [firstRoundedCandidate, not_exists.mp h, iInf_of_empty, iInf_top]
  obtain ⟨n, hn, heq⟩ := firstRoundedCandidate_attained Δ hΔ lam R a γ i hex
  have hu : roundUp Δ (passageSequence Δ lam R a γ i n) ≤ (T : ℝ≥0∞) := heq ▸ hle
  obtain ⟨hn', hround⟩ := goodPassage_prefix Δ hΔ lam R a hR γ γ' i T hpre n hn hu
  have hle' : firstRoundedCandidate Δ lam R a γ' i ≤ firstRoundedCandidate Δ lam R a γ i := by
    rw [heq, ← hround]
    exact iInf_le_of_le n (iInf_le_of_le hn' le_rfl)
  refine le_antisymm ?_ hle'
  refine le_iInf fun m => le_iInf fun hm => ?_
  by_cases hmT : roundUp Δ (passageSequence Δ lam R a γ' i m) ≤ (T : ℝ≥0∞)
  · obtain ⟨hm', hround'⟩ := goodPassage_prefix Δ hΔ lam R a hR γ' γ i T
      (fun t ht => (hpre t ht).symm) m hm hmT
    rw [← hround']
    exact iInf_le_of_le m (iInf_le_of_le hm' le_rfl)
  · exact hle.trans (le_of_lt (not_le.mp hmT))

/-- Every finite rounded candidate uses only the path up to its time
(`paper/main.tex:294–300`). -/
theorem roundedCandidateSequence_eq_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (z z' : CoupledSample d) (i : Fin d) (n : ℕ)
    (T : ℝ≥0) (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, z.1 t = z'.1 t)
    (hle : roundedCandidateSequence Δ lam R a z i n ≤ (T : ℝ≥0∞)) :
    roundedCandidateSequence Δ lam R a z i n =
      roundedCandidateSequence Δ lam R a z' i n := by
  induction n with
  | zero => exact firstRoundedCandidate_eq_of_prefix Δ hΔ lam R a hR z.1 z'.1 i T hpre hle
  | succ n ih =>
    have hprev : roundedCandidateSequence Δ lam R a z i n ≠ ⊤ := by
      intro ht
      rw [roundedCandidateSequence, if_pos ht] at hle
      exact (not_le_of_gt ENNReal.coe_lt_top) hle
    rw [roundedCandidateSequence, if_neg hprev] at hle
    have htT := (le_add_right le_rfl).trans hle
    have heq := ih htT
    have hprev' : roundedCandidateSequence Δ lam R a z' i n ≠ ⊤ := heq ▸ hprev
    set t := (roundedCandidateSequence Δ lam R a z i n).toNNReal with ht
    have htime : (t : ℝ≥0∞) = roundedCandidateSequence Δ lam R a z i n :=
      ENNReal.coe_toNNReal hprev
    have htT' : t ≤ T := ENNReal.coe_le_coe.mp (htime.symm ▸ htT)
    have hstep : firstRoundedCandidate Δ lam R (3 * lam * R) (pathTimeShift z.1 t) i ≤
        ((T - t : ℝ≥0) : ℝ≥0∞) := by
      apply (ENNReal.add_le_add_iff_left (a := (t : ℝ≥0∞)) ENNReal.coe_ne_top).mp
      rw [← ENNReal.coe_add, add_tsub_cancel_of_le htT', htime]
      exact hle
    have hshift : ∀ s ∈ Set.Icc (0 : ℝ≥0) (T - t),
        (pathTimeShift z.1 t) s = (pathTimeShift z'.1 t) s := by
      intro s hs
      exact hpre (t + s) ⟨zero_le, by
        calc t + s ≤ t + (T - t) := add_le_add le_rfl hs.2
          _ = T := add_tsub_cancel_of_le htT'⟩
    have hstepEq := firstRoundedCandidate_eq_of_prefix Δ hΔ lam R (3 * lam * R) hR
      (pathTimeShift z.1 t) (pathTimeShift z'.1 t) i (T - t) hshift hstep
    rw [roundedCandidateSequence, if_neg hprev, roundedCandidateSequence, if_neg hprev',
      ← heq]
    exact congrArg (fun s => roundedCandidateSequence Δ lam R a z i n + s) hstepEq

private theorem successfulCandidate_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (z z' : CoupledSample d) (i : Fin d) (T : ℝ≥0)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, z.1 t = z'.1 t)
    (hbits : ∀ k : ℕ, (k : ℝ≥0) * Δ ≤ T → z.2 k = z'.2 k) (n : ℕ)
    (hn : IsSuccessfulCandidate Δ lam R a z i n)
    (hle : roundedCandidateSequence Δ lam R a z i n ≤ (T : ℝ≥0∞)) :
    IsSuccessfulCandidate Δ lam R a z' i n ∧
      roundedCandidateSequence Δ lam R a z i n =
        roundedCandidateSequence Δ lam R a z' i n := by
  have heq := roundedCandidateSequence_eq_of_prefix Δ hΔ lam R a hR z z' i n T hpre hle
  obtain ⟨k, hk⟩ := roundedCandidateSequence_mem_grid Δ hΔ lam R a z i n hn.1
  have hkT : (k : ℝ≥0) * Δ ≤ T := ENNReal.coe_le_coe.mp (hk ▸ hle)
  refine ⟨⟨heq ▸ hn.1, ?_⟩, heq⟩
  have hb := hn.2
  rw [← heq, hk, ENNReal.toNNReal_coe, gridIndex_mul Δ hΔ k]
  rw [hk, ENNReal.toNNReal_coe, gridIndex_mul Δ hΔ k] at hb
  exact (hbits k hkT).symm.trans hb

/-- The successful candidate uses only the closed path window and the bits at candidate
grid times in that window (`paper/main.tex:297–300,353–364`). -/
theorem firstSuccessfulCandidate_eq_of_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (z z' : CoupledSample d) (i : Fin d) (T : ℝ≥0)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, z.1 t = z'.1 t)
    (hbits : ∀ k : ℕ, (k : ℝ≥0) * Δ ≤ T → z.2 k = z'.2 k)
    (hle : firstSuccessfulCandidate Δ lam R a z i ≤ (T : ℝ≥0∞)) :
    firstSuccessfulCandidate Δ lam R a z i = firstSuccessfulCandidate Δ lam R a z' i := by
  have hfin : firstSuccessfulCandidate Δ lam R a z i ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  obtain ⟨n, hn, heq⟩ := firstSuccessfulCandidate_attained Δ hΔ lam R a z i hfin
  obtain ⟨hn', heq'⟩ := successfulCandidate_prefix Δ hΔ lam R a hR z z' i T
    hpre hbits n hn (heq ▸ hle)
  have hle' : firstSuccessfulCandidate Δ lam R a z' i ≤ firstSuccessfulCandidate Δ lam R a z i := by
    rw [heq, heq']
    exact iInf_le_of_le n (iInf_le_of_le hn' le_rfl)
  refine le_antisymm ?_ hle'
  refine le_iInf fun m => le_iInf fun hm => ?_
  by_cases hmT : roundedCandidateSequence Δ lam R a z' i m ≤ (T : ℝ≥0∞)
  · obtain ⟨hm', hmeq⟩ := successfulCandidate_prefix Δ hΔ lam R a hR z' z i T
      (fun t ht => (hpre t ht).symm) (fun k hk => (hbits k hk).symm) m hm hmT
    rw [hmeq]
    exact iInf_le_of_le m (iInf_le_of_le hm' le_rfl)
  · exact hle.trans (le_of_lt (not_le.mp hmT))


end EinsteinRelation.Regeneration
