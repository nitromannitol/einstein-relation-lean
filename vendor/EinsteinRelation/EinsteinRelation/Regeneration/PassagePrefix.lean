import EinsteinRelation.Regeneration.Geometry
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-! # Actual passage-prefix nonanticipativity

Source `paper/main.tex:283–294,353–370` (the finite-history event `Gamma_n`).
Two paths that agree on the closed window `[0, T]` have the same actual passage
times up to the level `T`: `V_n ≤ T` holds for one path exactly when it holds for
the other, and then the two passage times coincide. The proof inducts on `n`
through the closed first-hit characterization and the rounded recursion. It uses
no whole-path equality, no finite-hit premise, and no chronology premise.
-/

namespace EinsteinRelation.Regeneration

/-- Closed-window prefix locality of the first hit above a level: if the first hit is
at most `T`, the first hit of the other path is also bounded by the same level. -/
private theorem firstHittingAbove_le_of_prefix_eq {d : ℕ} (γ γ' : Path d) (i : Fin d)
    (a : ℝ) (T : ℝ≥0) (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, γ t = γ' t)
    (hle : firstHittingAbove γ i a ≤ (T : ℝ≥0∞)) :
    firstHittingAbove γ i a ≤ firstHittingAbove γ' i a := by
  have h0 : (0 : ℝ≥0) ∈ Set.Icc (0 : ℝ≥0) T := ⟨le_rfl, zero_le⟩
  unfold firstHittingAbove
  refine le_iInf₂ fun t ht => ?_
  by_cases htT : t ≤ T
  · have hγ : a ≤ γ t i - γ 0 i := by
      rw [hpre t ⟨zero_le, htT⟩, hpre 0 h0]
      exact ht
    exact iInf_le_of_le t (iInf_le_of_le hγ le_rfl)
  · exact hle.trans (ENNReal.coe_le_coe.mpr (not_le.mp htT).le)

/-- The closed sublevel event `{first hit ≤ T}` is determined by the path on `[0, T]`. -/
private theorem firstHittingAbove_le_iff_of_prefix_eq {d : ℕ} (γ γ' : Path d) (i : Fin d)
    (a : ℝ) (T : ℝ≥0) (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, γ t = γ' t) :
    firstHittingAbove γ i a ≤ (T : ℝ≥0∞) ↔ firstHittingAbove γ' i a ≤ (T : ℝ≥0∞) := by
  have h0 : (0 : ℝ≥0) ∈ Set.Icc (0 : ℝ≥0) T := ⟨le_rfl, zero_le⟩
  rw [firstHittingAbove_le_iff, firstHittingAbove_le_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, ?_⟩
    rw [← hpre t ht, ← hpre 0 h0]
    exact h
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, ?_⟩
    rw [hpre t ht, hpre 0 h0]
    exact h

/-- Under a closed-window prefix equality, a first hit at most `T` is equal for both paths. -/
private theorem firstHittingAbove_eq_of_prefix_eq {d : ℕ} (γ γ' : Path d) (i : Fin d)
    (a : ℝ) (T : ℝ≥0) (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, γ t = γ' t)
    (hle : firstHittingAbove γ i a ≤ (T : ℝ≥0∞)) :
    firstHittingAbove γ i a = firstHittingAbove γ' i a :=
  le_antisymm (firstHittingAbove_le_of_prefix_eq γ γ' i a T hpre hle)
    (firstHittingAbove_le_of_prefix_eq γ' γ i a T (fun t ht => (hpre t ht).symm)
      ((firstHittingAbove_le_iff_of_prefix_eq γ γ' i a T hpre).mp hle))

/-- The running coordinate maximum at a time `t ≤ T` depends only on the path on `[0, T]`. -/
private theorem coordinateMaximum_eq_of_prefix_eq {d : ℕ} (γ γ' : Path d) (i : Fin d)
    (T t : ℝ≥0) (ht : t ≤ T) (hpre : ∀ s ∈ Set.Icc (0 : ℝ≥0) T, γ s = γ' s) :
    coordinateMaximum γ i t = coordinateMaximum γ' i t := by
  have h0 : (0 : ℝ≥0) ∈ Set.Icc (0 : ℝ≥0) T := ⟨le_rfl, zero_le⟩
  unfold coordinateMaximum
  congr 1
  refine Set.image_congr fun s hs => ?_
  have hsT : s ∈ Set.Icc (0 : ℝ≥0) T := ⟨hs.1, hs.2.trans ht⟩
  show γ s i - γ 0 i = γ' s i - γ' 0 i
  rw [hpre s hsT, hpre 0 h0]

private theorem passageSequence_zero {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (γ : Path d)
    (i : Fin d) : passageSequence Δ lam R a γ i 0 = firstHittingAbove γ i (a / lam) := by
  rw [passageSequence]

private theorem passageSequence_succ_of_top {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (γ : Path d)
    (i : Fin d) (n : ℕ) (h : roundUp Δ (passageSequence Δ lam R a γ i n) = ⊤) :
    passageSequence Δ lam R a γ i (n + 1) = ⊤ := by
  rw [passageSequence, if_pos h]

private theorem passageSequence_succ_of_ne_top {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) (n : ℕ)
    (h : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤) :
    passageSequence Δ lam R a γ i (n + 1) =
      firstHittingAbove γ i (coordinateMaximum γ i
        (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal + R) := by
  rw [passageSequence, if_neg h]

/-- One-sided induction: a passage time at most `T` for `γ` is at most `T` for `γ'`, and
the two passage times agree. Each step uses only the previous exact time, the rounded
time, and the first hit at the resulting coordinate maximum. -/
private theorem passageSequence_le_imp_of_prefix_eq {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (γ γ' : Path d) (i : Fin d) (T : ℝ≥0)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, γ t = γ' t) (n : ℕ) :
    passageSequence Δ lam R a γ i n ≤ (T : ℝ≥0∞) →
      passageSequence Δ lam R a γ' i n ≤ (T : ℝ≥0∞) ∧
        passageSequence Δ lam R a γ i n = passageSequence Δ lam R a γ' i n := by
  induction n with
  | zero =>
    intro hle
    simp only [passageSequence_zero] at hle ⊢
    exact ⟨(firstHittingAbove_le_iff_of_prefix_eq γ γ' i (a / lam) T hpre).mp hle,
      firstHittingAbove_eq_of_prefix_eq γ γ' i (a / lam) T hpre hle⟩
  | succ n ih =>
    intro hle
    -- A finite next passage at most `T` forces a finite rounded predecessor below `T`.
    have hne : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤ := by
      intro htop
      rw [passageSequence_succ_of_top Δ lam R a γ i n htop] at hle
      exact absurd hle (not_le.mpr ENNReal.coe_lt_top)
    have hprev : roundUp Δ (passageSequence Δ lam R a γ i n) < (T : ℝ≥0∞) :=
      (rounded_passage_lt_next Δ lam R a hR γ i n hne).trans_le hle
    have hSle : passageSequence Δ lam R a γ i n ≤ (T : ℝ≥0∞) :=
      (le_roundUp Δ hΔ (passageSequence Δ lam R a γ i n)).trans hprev.le
    obtain ⟨-, hSeq⟩ := ih hSle
    have hround : roundUp Δ (passageSequence Δ lam R a γ' i n) =
        roundUp Δ (passageSequence Δ lam R a γ i n) := by
      rw [hSeq]
    have hne' : roundUp Δ (passageSequence Δ lam R a γ' i n) ≠ ⊤ := by
      rw [hround]
      exact hne
    have hu : (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal ≤ T := by
      have h' : ((roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal : ℝ≥0∞) ≤
          (T : ℝ≥0∞) := by
        rw [ENNReal.coe_toNNReal hne]
        exact hprev.le
      exact ENNReal.coe_le_coe.mp h'
    have hCM := coordinateMaximum_eq_of_prefix_eq γ γ' i T _ hu hpre
    have hγ := passageSequence_succ_of_ne_top Δ lam R a γ i n hne
    have hγ' := passageSequence_succ_of_ne_top Δ lam R a γ' i n hne'
    rw [hround, ← hCM] at hγ'
    rw [hγ] at hle
    have hle' := (firstHittingAbove_le_iff_of_prefix_eq γ γ' i _ T hpre).mp hle
    refine ⟨?_, ?_⟩
    · rw [hγ']
      exact hle'
    · rw [hγ, hγ']
      exact firstHittingAbove_eq_of_prefix_eq γ γ' i _ T hpre hle

/-- Source `paper/main.tex:283–294,353–370`: two paths that agree on `[0, T]` have the
same actual passage time `V_n` at the level `T` and the same value whenever `V_n ≤ T`. -/
theorem passageSequence_prefix_determined {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (γ γ' : Path d) (i : Fin d) (n : ℕ) (T : ℝ≥0)
    (hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) T, γ t = γ' t) :
    (passageSequence Δ lam R a γ i n ≤ (T : ℝ≥0∞) ↔
      passageSequence Δ lam R a γ' i n ≤ (T : ℝ≥0∞)) ∧
    (passageSequence Δ lam R a γ i n ≤ (T : ℝ≥0∞) →
      passageSequence Δ lam R a γ i n = passageSequence Δ lam R a γ' i n) := by
  have hfwd := passageSequence_le_imp_of_prefix_eq Δ hΔ lam R a hR γ γ' i T hpre n
  have hbwd := passageSequence_le_imp_of_prefix_eq Δ hΔ lam R a hR γ' γ i T
    (fun t ht => (hpre t ht).symm) n
  exact ⟨⟨fun hle => (hfwd hle).1, fun hle' => (hbwd hle').1⟩, fun hle => (hfwd hle).2⟩

end EinsteinRelation.Regeneration
