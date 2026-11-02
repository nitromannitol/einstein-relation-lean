import EinsteinRelation.Regeneration.Geometry

open MeasureTheory
open scoped NNReal ENNReal

/-! # Actual passage heights of the good-passage construction

Source `paper/main.tex:283–299,365–374`. The level sequence `V_j(a)` and the first
rounded candidate `Ñ_1(a)` are the unchanged actual definitions; the statements
below are frozen, and only proof bodies and private helpers are added here.
-/

namespace EinsteinRelation.Regeneration

/-- A finite attained first hitting time is a genuine crossing at that time. -/
private theorem crossing_at_firstHittingAbove {d : ℕ} (γ : Path d) (i : Fin d)
    (a : ℝ) (V : ℝ≥0) (hV : firstHittingAbove γ i a = (V : ℝ≥0∞)) :
    a ≤ γ V i - γ 0 i := by
  obtain ⟨u, hu, hcross⟩ := (firstHittingAbove_le_iff γ i a V).mp hV.le
  have htime := firstHittingAbove_le_of_crossing γ i a u hcross
  rw [hV] at htime
  have huV : u = V := le_antisymm hu.2 (ENNReal.coe_le_coe.mp htime)
  simpa only [huV] using hcross

/-- A finite time never exceeds its finite rounded-up time. -/
private theorem toNNReal_le_roundUp_toNNReal (Δ : ℝ≥0) (hΔ : 0 < Δ) (t : ℝ≥0∞)
    (ht : t ≠ ⊤) (hround : roundUp Δ t ≠ ⊤) :
    t.toNNReal ≤ (roundUp Δ t).toNNReal := by
  apply ENNReal.coe_le_coe.mp
  simpa only [ENNReal.coe_toNNReal ht, ENNReal.coe_toNNReal hround] using le_roundUp Δ hΔ t

/-- Induction on the level sequence: each finite passage time lies at or above `a / lam`. -/
private theorem passage_level_le_of_finite {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 ≤ R) (γ : Path d) (i : Fin d) (n : ℕ) :
    passageSequence Δ lam R a γ i n ≠ ⊤ →
      a / lam ≤ γ (passageSequence Δ lam R a γ i n).toNNReal i - γ 0 i := by
  induction n with
  | zero =>
    intro hfinite
    have h0 : passageSequence Δ lam R a γ i 0 = firstHittingAbove γ i (a / lam) := by
      rw [passageSequence]
    rw [h0] at hfinite ⊢
    exact crossing_at_firstHittingAbove γ i (a / lam) _ (ENNReal.coe_toNNReal hfinite).symm
  | succ m ih =>
    intro hfinite
    have hround : roundUp Δ (passageSequence Δ lam R a γ i m) ≠ ⊤ := by
      intro ht
      apply hfinite
      rw [passageSequence, if_pos ht]
    have hmfin : passageSequence Δ lam R a γ i m ≠ ⊤ := by
      intro ht
      apply hround
      simp [ht, roundUp]
    have hprev := ih hmfin
    have hdisp := displacement_le_coordinateMaximum γ i _ _
      (toNNReal_le_roundUp_toNNReal Δ hΔ _ hmfin hround)
    have hstep : passageSequence Δ lam R a γ i (m + 1) =
        firstHittingAbove γ i (coordinateMaximum γ i
          (roundUp Δ (passageSequence Δ lam R a γ i m)).toNNReal + R) := by
      rw [passageSequence, if_neg hround]
    have hV : firstHittingAbove γ i (coordinateMaximum γ i
          (roundUp Δ (passageSequence Δ lam R a γ i m)).toNNReal + R) =
        ((passageSequence Δ lam R a γ i (m + 1)).toNNReal : ℝ≥0∞) := by
      rw [← hstep, ENNReal.coe_toNNReal hfinite]
    have hcross := crossing_at_firstHittingAbove γ i _ _ hV
    linarith

/-- Finite passage heights stay at least `a / lam` above the starting point. -/
theorem initial_level_le_at_passage {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 ≤ R) (γ : Path d) (i : Fin d) (n : ℕ)
    (hfinite : passageSequence Δ lam R a γ i n ≠ ⊤) :
    a / lam ≤ γ (passageSequence Δ lam R a γ i n).toNNReal i - γ 0 i :=
  passage_level_le_of_finite Δ hΔ lam R a hR γ i n hfinite

/-- A finite first rounded candidate is at least `a / lam - R / 2` above the start. -/
theorem firstRoundedCandidate_height_lower_bound {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 ≤ R) (γ : Path d) (i : Fin d)
    (hfinite : firstRoundedCandidate Δ lam R a γ i ≠ ⊤) :
    a / lam - R / 2 ≤ γ (firstRoundedCandidate Δ lam R a γ i).toNNReal i - γ 0 i := by
  have hex : ∃ n : ℕ, IsGoodPassage Δ lam R a γ i n := by
    by_contra hnone
    have hno : ∀ n : ℕ, ¬ IsGoodPassage Δ lam R a γ i n := not_exists.mp hnone
    have htop : firstRoundedCandidate Δ lam R a γ i = ⊤ := by
      rw [firstRoundedCandidate]
      simp only [hno, iInf_of_empty, iInf_top]
    exact hfinite htop
  obtain ⟨n, hn, htime⟩ := firstRoundedCandidate_attained Δ hΔ lam R a γ i hex
  have hVfin : passageSequence Δ lam R a γ i n ≠ ⊤ := hn.1
  have hUfin : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤ := hn.2.1
  have hlow := initial_level_le_at_passage Δ hΔ lam R a hR γ i n hVfin
  have hle := toNNReal_le_roundUp_toNNReal Δ hΔ _ hVfin hUfin
  have hosc : ∀ s ∈ Set.Icc (passageSequence Δ lam R a γ i n).toNNReal
      (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal,
      |γ s i - γ (passageSequence Δ lam R a γ i n).toNNReal i| ≤ R / 2 := hn.2.2
  obtain ⟨hU1, _⟩ := abs_le.mp
    (hosc (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal ⟨hle, le_rfl⟩)
  rw [htime]
  linarith

end EinsteinRelation.Regeneration
