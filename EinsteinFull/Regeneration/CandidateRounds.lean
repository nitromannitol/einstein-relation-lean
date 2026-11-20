import EinsteinFull.Regeneration.FirstCandidateMoment
import EinsteinRelation.Regeneration.CandidateGrid
import EinsteinRelation.Regeneration.OneIntervalLocality

/-!
# Rounds of a candidate search

A candidate search runs through its rounded candidates; at each candidate a coin is
tossed and a failed coin starts a new search at level `3R` above the candidate. The
weight of `N` failed rounds is the exponential height of the `N`th candidate above
the search level, on the event that the earlier coins failed. One more failed
round multiplies this weight by the weight of a failed coin followed by a first
rounded candidate of the search restarted at the candidate. Under the support
property of the successful bridges, the exponential overshoot of the successful
candidate is dominated by the sum of the failed-round weights.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The weight of `N` failed rounds of a candidate search at level `L`. -/
noncomputable def failedRoundWeight {d : ℕ} (Δ : ℝ≥0) (lam R L b : ℝ) (i : Fin d) (N : ℕ)
    (w : CoupledSample d) : ℝ≥0∞ :=
  {w : CoupledSample d | roundedCandidateSequence Δ lam R L w i N ≠ ⊤ ∧
      ∀ j < N, w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) = false}.indicator
    (fun w => ENNReal.ofReal (Real.exp (b * lam *
      (w.1 (roundedCandidateSequence Δ lam R L w i N).toNNReal i - w.1 0 i - L / lam)))) w

/-- The weight of a failed coin followed by the first rounded candidate of the search
restarted at level `3R`. -/
noncomputable def failedCoinWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d)
    (v : CoupledSample d) : ℝ≥0∞ :=
  {v : CoupledSample d | v.2 0 = false ∧
      firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i ≠ ⊤}.indicator
    (fun v => ENNReal.ofReal (Real.exp (b * lam *
      (v.1 (firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i).toNNReal i - v.1 0 i)))) v

/-- The exponential overshoot of the successful candidate of a search at level `L`,
measured at the end of its bridge. -/
noncomputable def candidateOvershootWeight {d : ℕ} (Δ : ℝ≥0) (lam R L b : ℝ) (i : Fin d)
    (w : CoupledSample d) : ℝ≥0∞ :=
  {w : CoupledSample d | firstSuccessfulCandidate Δ lam R L w i ≠ ⊤}.indicator
    (fun w => ENNReal.ofReal (Real.exp (b * lam *
      (w.1 (firstSuccessfulCandidate Δ lam R L w i + Δ).toNNReal i - w.1 0 i - L / lam)))) w

/-- Successive rounded candidates are at least one grid step apart. -/
theorem roundedCandidateSequence_add_step_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R L : ℝ) (hlam : 0 < lam) (hR : 0 < R) (w : CoupledSample d) (i : Fin d)
    (j : ℕ) : roundedCandidateSequence Δ lam R L w i j + Δ ≤
      roundedCandidateSequence Δ lam R L w i (j + 1) := by
  by_cases htop : roundedCandidateSequence Δ lam R L w i j = ⊤
  · rw [htop, top_add]
    rw [roundedCandidateSequence, ite_eq_left htop]
  · rw [roundedCandidateSequence, ite_eq_right htop]
    have hpos : 0 < (3 * lam * R) / lam :=
      div_pos (mul_pos (mul_pos (by norm_num) hlam) hR) hlam
    exact add_le_add le_rfl (step_le_firstRoundedCandidate Δ hΔ lam R (3 * lam * R) hR hpos
      (pathTimeShift w.1 (roundedCandidateSequence Δ lam R L w i j).toNNReal) i)

/-- Earlier rounded candidates are strictly earlier when the later one is finite. -/
theorem roundedCandidateSequence_lt_of_lt {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R L : ℝ) (hlam : 0 < lam) (hR : 0 < R) (w : CoupledSample d) (i : Fin d)
    {j n : ℕ} (hjn : j < n) (hfin : roundedCandidateSequence Δ lam R L w i n ≠ ⊤) :
    roundedCandidateSequence Δ lam R L w i j < roundedCandidateSequence Δ lam R L w i n := by
  induction n with
  | zero => exact absurd hjn (Nat.not_lt_zero j)
  | succ n ih =>
    have hstep := roundedCandidateSequence_add_step_le Δ hΔ lam R L hlam hR w i n
    have hnfin : roundedCandidateSequence Δ lam R L w i n ≠ ⊤ :=
      ne_top_of_le_ne_top hfin ((le_add_right le_rfl).trans hstep)
    have hlt : roundedCandidateSequence Δ lam R L w i n <
        roundedCandidateSequence Δ lam R L w i (n + 1) :=
      lt_of_lt_of_le (ENNReal.lt_add_right hnfin (by exact_mod_cast hΔ.ne')) hstep
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with h | h
    · exact (ih h hnfin).trans hlt
    · rw [h]
      exact hlt


/-- One more failed round multiplies the weight by the failed-coin weight of the
sample shifted to the last candidate. -/
theorem failedRoundWeight_succ_le {d : ℕ} (Δ : ℝ≥0) (lam R L b : ℝ)
    (i : Fin d) (N : ℕ) (w : CoupledSample d) :
    failedRoundWeight Δ lam R L b i (N + 1) w ≤
      failedRoundWeight Δ lam R L b i N w *
        failedCoinWeight Δ lam R b i
          (sampleTimeShift Δ w (roundedCandidateSequence Δ lam R L w i N).toNNReal) := by
  set C := roundedCandidateSequence Δ lam R L w i with hC
  by_cases hcond : C (N + 1) ≠ ⊤ ∧ ∀ j < N + 1, w.2 (gridIndex Δ (C j).toNNReal) = false
  · obtain ⟨hfin, hbits⟩ := hcond
    have hNfin : C N ≠ ⊤ := by
      intro htop
      apply hfin
      rw [hC, roundedCandidateSequence, ite_eq_left htop]
    have hsucc : C (N + 1) = C N + firstRoundedCandidate Δ lam R (3 * lam * R)
        (pathTimeShift w.1 (C N).toNNReal) i := by
      rw [hC, roundedCandidateSequence, ite_eq_right hNfin]
    set F := firstRoundedCandidate Δ lam R (3 * lam * R) (pathTimeShift w.1 (C N).toNNReal) i
      with hF
    have hFfin : F ≠ ⊤ := by
      intro htop
      apply hfin
      rw [hsucc, htop, add_top]
    have htime : (C (N + 1)).toNNReal = (C N).toNNReal + F.toNNReal := by
      rw [hsucc, ENNReal.toNNReal_add hNfin hFfin]
    have hmemL : w ∈ {w : CoupledSample d | roundedCandidateSequence Δ lam R L w i (N + 1) ≠ ⊤ ∧
        ∀ j < N + 1, w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) =
          false} := ⟨hfin, hbits⟩
    have hmemN : w ∈ {w : CoupledSample d | roundedCandidateSequence Δ lam R L w i N ≠ ⊤ ∧
        ∀ j < N, w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) =
          false} := ⟨hNfin, fun j hj => hbits j (Nat.lt_succ_of_lt hj)⟩
    have hmemC : sampleTimeShift Δ w (C N).toNNReal ∈ {v : CoupledSample d | v.2 0 = false ∧
        firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i ≠ ⊤} := by
      refine ⟨?_, hFfin⟩
      change w.2 (gridIndex Δ (C N).toNNReal + 0) = false
      rw [add_zero]
      exact hbits N (Nat.lt_succ_self N)
    simp only [failedRoundWeight, failedCoinWeight]
    rw [Set.indicator_of_mem hmemL, Set.indicator_of_mem hmemN, Set.indicator_of_mem hmemC,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    apply le_of_eq
    congr 2
    change b * lam * (w.1 (C (N + 1)).toNNReal i - w.1 0 i - L / lam) =
      b * lam * (w.1 (C N).toNNReal i - w.1 0 i - L / lam) +
        b * lam * (w.1 ((C N).toNNReal + F.toNNReal) i - w.1 ((C N).toNNReal + 0) i)
    rw [htime, add_zero]
    ring
  · simp only [failedRoundWeight]
    rw [Set.indicator_of_notMem (show w ∉ {w : CoupledSample d |
        roundedCandidateSequence Δ lam R L w i (N + 1) ≠ ⊤ ∧
        ∀ j < N + 1, w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) =
          false} from hcond)]
    exact zero_le

/-- Under the support property of the successful bridges, the overshoot weight of the
successful candidate is dominated by the failed-round weights. -/
theorem candidateOvershootWeight_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R L b : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (hb : 0 ≤ b) (i : Fin d) (w : CoupledSample d)
    (hbridge : ∀ n : ℕ, w.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        w.1 t ∈ couplingRegion i R (w.1 ((n : ℝ≥0) * Δ))) :
    candidateOvershootWeight Δ lam R L b i w ≤
      ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
        ∑' N, failedRoundWeight Δ lam R L b i N w := by
  set C := roundedCandidateSequence Δ lam R L w i with hC
  by_cases hfin : firstSuccessfulCandidate Δ lam R L w i ≠ ⊤
  · obtain ⟨n, hn, heq⟩ := firstSuccessfulCandidate_attained Δ hΔ lam R L w i hfin
    obtain ⟨hnfin, hbit⟩ := hn
    have hfail : ∀ j < n, w.2 (gridIndex Δ (C j).toNNReal) = false := by
      intro j hj
      by_contra hbitj
      have hsucc : IsSuccessfulCandidate Δ lam R L w i j := by
        refine ⟨ne_top_of_lt (roundedCandidateSequence_lt_of_lt Δ hΔ lam R L hlam hR w i hj
          hnfin), ?_⟩
        simpa using hbitj
      have hle : firstSuccessfulCandidate Δ lam R L w i ≤ C j :=
        iInf_le_of_le j (iInf_le_of_le hsucc le_rfl)
      have hlt := roundedCandidateSequence_lt_of_lt Δ hΔ lam R L hlam hR w i hj hnfin
      rw [heq] at hle
      exact absurd hle (not_le_of_gt hlt)
    obtain ⟨k, hk⟩ := roundedCandidateSequence_mem_grid Δ hΔ lam R L w i n hnfin
    have hbitk : w.2 k = true := by
      have h := hbit
      simp only [hk, ENNReal.toNNReal_coe, gridIndex_mul Δ hΔ] at h
      exact h
    have hregion := hbridge k hbitk (((k + 1 : ℕ) : ℝ≥0) * Δ)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) zero_le) le_rfl
    have hbound := (couplingRegion_coordinate_bounds i R _ _ hregion).2
    have hend : (firstSuccessfulCandidate Δ lam R L w i + Δ).toNNReal =
        ((k + 1 : ℕ) : ℝ≥0) * Δ := by
      rw [heq, hk, ← ENNReal.coe_add, ENNReal.toNNReal_coe]
      push_cast
      ring
    have hCn : (C n).toNNReal = (k : ℝ≥0) * Δ := by
      rw [show C n = roundedCandidateSequence Δ lam R L w i n from rfl, hk, ENNReal.toNNReal_coe]
    have hmem : w ∈ {w : CoupledSample d | firstSuccessfulCandidate Δ lam R L w i ≠ ⊤} := hfin
    have hmemN : w ∈ {w : CoupledSample d | roundedCandidateSequence Δ lam R L w i n ≠ ⊤ ∧
        ∀ j < n, w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) =
          false} := ⟨hnfin, hfail⟩
    have hYn : failedRoundWeight Δ lam R L b i n w = ENNReal.ofReal (Real.exp (b * lam *
        (w.1 (C n).toNNReal i - w.1 0 i - L / lam))) := by
      simp only [failedRoundWeight]
      exact Set.indicator_of_mem hmemN _
    simp only [candidateOvershootWeight]
    rw [Set.indicator_of_mem hmem]
    calc ENNReal.ofReal (Real.exp (b * lam *
          (w.1 (firstSuccessfulCandidate Δ lam R L w i + Δ).toNNReal i - w.1 0 i - L / lam)))
        ≤ ENNReal.ofReal (Real.exp (b * lam * (11 * R)) *
          Real.exp (b * lam * (w.1 (C n).toNNReal i - w.1 0 i - L / lam))) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← Real.exp_add, hend, hCn]
          apply Real.exp_le_exp.mpr
          have hbl : 0 ≤ b * lam := mul_nonneg hb hlam.le
          nlinarith
      _ = ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
          failedRoundWeight Δ lam R L b i n w := by
          rw [hYn, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ _ := by
          gcongr
          exact ENNReal.le_tsum (f := fun N => failedRoundWeight Δ lam R L b i N w) n
  · simp only [candidateOvershootWeight]
    rw [Set.indicator_of_notMem (show w ∉ {w : CoupledSample d |
      firstSuccessfulCandidate Δ lam R L w i ≠ ⊤} from hfin)]
    exact zero_le

end EinsteinFull.Regeneration
