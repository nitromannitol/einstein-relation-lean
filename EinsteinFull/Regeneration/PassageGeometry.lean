import EinsteinRelation.Regeneration.Chronology
import EinsteinRelation.Regeneration.ShiftedMaximum
import EinsteinRelation.Regeneration.Geometry

/-!
# Geometry of the passages of a candidate search

At a first hitting time of a nonnegative level, the coordinate displacement equals
the level and the running maximum equals the displacement. Consequently each new
passage of a candidate search lies at most one window maximum plus `R` above the
previous one, a failed guard means that the path moves by more than `R / 2`
within one regeneration interval after the passage, and the first rounded
candidate is the rounding of the first good passage.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- At the first hitting time of a nonnegative level, the displacement is at most
the level. -/
theorem displacement_le_of_firstHittingAbove {d : ℕ} (γ : Path d) (i : Fin d)
    (h : ℝ) (hh : 0 ≤ h) (V : ℝ≥0) (hV : firstHittingAbove γ i h = (V : ℝ≥0∞)) :
    γ V i - γ 0 i ≤ h := by
  by_contra hlt
  push Not at hlt
  have hc : ContinuousOn (fun s : ℝ≥0 => γ s i - γ 0 i) (Set.Icc 0 V) :=
    (((continuous_apply i).comp γ.continuous).sub continuous_const).continuousOn
  have hmem : h ∈ Set.Icc ((fun s : ℝ≥0 => γ s i - γ 0 i) 0)
      ((fun s : ℝ≥0 => γ s i - γ 0 i) V) := by
    refine ⟨by simpa using hh, hlt.le⟩
  obtain ⟨s, hs, hsval⟩ := intermediate_value_Icc zero_le hc hmem
  have hsV : s ≠ V := by
    rintro rfl
    exact absurd hsval (ne_of_lt hlt).symm
  have hslt : s < V := lt_of_le_of_ne hs.2 hsV
  have hle := firstHittingAbove_le_of_crossing γ i h s (le_of_eq hsval.symm)
  rw [hV] at hle
  exact absurd (ENNReal.coe_le_coe.mp hle) (not_le_of_gt hslt)

/-- At the first hitting time of a nonnegative level, the displacement equals the
level. -/
theorem displacement_eq_of_firstHittingAbove {d : ℕ} (γ : Path d) (i : Fin d)
    (h : ℝ) (hh : 0 ≤ h) (V : ℝ≥0) (hV : firstHittingAbove γ i h = (V : ℝ≥0∞)) :
    γ V i - γ 0 i = h := by
  refine le_antisymm (displacement_le_of_firstHittingAbove γ i h hh V hV) ?_
  obtain ⟨u, hu, hcross⟩ := (firstHittingAbove_le_iff γ i h V).mp hV.le
  have htime := firstHittingAbove_le_of_crossing γ i h u hcross
  rw [hV] at htime
  have huV : u = V := le_antisymm hu.2 (ENNReal.coe_le_coe.mp htime)
  simpa only [huV] using hcross

/-- The running maximum at a first hitting time is the displacement there. -/
theorem coordinateMaximum_eq_of_firstHittingAbove {d : ℕ} (γ : Path d) (i : Fin d)
    (h : ℝ) (V : ℝ≥0) (hV : firstHittingAbove γ i h = (V : ℝ≥0∞)) :
    coordinateMaximum γ i V = γ V i - γ 0 i := by
  refine le_antisymm ?_ (displacement_le_coordinateMaximum γ i V V le_rfl)
  apply coordinateMaximum_le
  intro s hs
  have h := coordinate_le_at_firstHittingAbove γ i h V hV s hs.2
  linarith

/-- A finite time is at most one grid step before its rounding. -/
theorem roundUp_toNNReal_le_add_step (Δ : ℝ≥0) (hΔ : 0 < Δ) (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    (roundUp Δ t).toNNReal ≤ t.toNNReal + Δ := by
  rw [roundUp, ite_eq_right ht, ENNReal.toNNReal_coe]
  apply NNReal.coe_le_coe.mp
  change (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ) * (Δ : ℝ) ≤ t.toReal + (Δ : ℝ)
  have hΔR : (0 : ℝ) < Δ := NNReal.coe_pos.mpr hΔ
  have hq : 0 ≤ t.toReal / (Δ : ℝ) := div_nonneg ENNReal.toReal_nonneg hΔR.le
  have hc : (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ) < t.toReal / (Δ : ℝ) + 1 :=
    Nat.ceil_lt_add_one hq
  have hmul := mul_lt_mul_of_pos_right hc hΔR
  rw [add_mul, div_mul_cancel₀ _ hΔR.ne', one_mul] at hmul
  exact hmul.le

/-- The displacement at a finite passage of positive index is the running maximum at
the previous rounded passage plus `R`. -/
theorem passage_displacement_succ {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (hR : 0 < R)
    (γ : Path d) (i : Fin d) (n : ℕ)
    (hfin : passageSequence Δ lam R a γ i (n + 1) ≠ ⊤) :
    roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤ ∧
    γ (passageSequence Δ lam R a γ i (n + 1)).toNNReal i - γ 0 i =
      coordinateMaximum γ i (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal + R := by
  have hround : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤ := by
    intro htop
    apply hfin
    rw [passageSequence, ite_eq_left htop]
  refine ⟨hround, ?_⟩
  have hdef : passageSequence Δ lam R a γ i (n + 1) = firstHittingAbove γ i
      (coordinateMaximum γ i (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal + R) := by
    rw [passageSequence, ite_eq_right hround]
  have hlevel : 0 ≤ coordinateMaximum γ i
      (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal + R :=
    add_nonneg (coordinateMaximum_nonneg γ i _) hR.le
  apply displacement_eq_of_firstHittingAbove γ i _ hlevel
  rw [← hdef, ENNReal.coe_toNNReal hfin]

/-- The displacement at the first passage is the initial level. -/
theorem passage_displacement_zero {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) (ha : 0 ≤ a / lam)
    (γ : Path d) (i : Fin d) (hfin : passageSequence Δ lam R a γ i 0 ≠ ⊤) :
    γ (passageSequence Δ lam R a γ i 0).toNNReal i - γ 0 i = a / lam := by
  apply displacement_eq_of_firstHittingAbove γ i _ ha
  rw [ENNReal.coe_toNNReal hfin]
  rfl

/-- The running maximum at a finite passage is the displacement there. -/
theorem coordinateMaximum_at_passage {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) (n : ℕ) (hfin : passageSequence Δ lam R a γ i n ≠ ⊤) :
    coordinateMaximum γ i (passageSequence Δ lam R a γ i n).toNNReal =
      γ (passageSequence Δ lam R a γ i n).toNNReal i - γ 0 i := by
  cases n with
  | zero =>
    apply coordinateMaximum_eq_of_firstHittingAbove γ i (a / lam)
    rw [ENNReal.coe_toNNReal hfin]
    rfl
  | succ n =>
    have hround : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤ := by
      intro htop
      apply hfin
      rw [passageSequence, ite_eq_left htop]
    apply coordinateMaximum_eq_of_firstHittingAbove γ i
      (coordinateMaximum γ i (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal + R)
    rw [ENNReal.coe_toNNReal hfin, passageSequence, ite_eq_right hround]

/-- The running maximum is monotone in time. -/
theorem coordinateMaximum_mono {d : ℕ} (γ : Path d) (i : Fin d) {s t : ℝ≥0} (hst : s ≤ t) :
    coordinateMaximum γ i s ≤ coordinateMaximum γ i t := by
  apply coordinateMaximum_le
  intro u hu
  exact displacement_le_coordinateMaximum γ i u t (hu.2.trans hst)

/-- The running maximum at the rounding of a finite passage exceeds the displacement
at the passage by at most the window maximum after the passage. -/
theorem coordinateMaximum_roundUp_passage_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (γ : Path d) (i : Fin d) (n : ℕ)
    (hfin : passageSequence Δ lam R a γ i n ≠ ⊤) :
    coordinateMaximum γ i (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal ≤
      γ (passageSequence Δ lam R a γ i n).toNNReal i - γ 0 i +
        coordinateMaximum
          (pathTimeShift γ (passageSequence Δ lam R a γ i n).toNNReal) i Δ := by
  set V := (passageSequence Δ lam R a γ i n).toNNReal with hVdef
  set U := (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal with hUdef
  have hround : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤ := by
    rw [roundUp, ite_eq_right hfin]
    exact ENNReal.coe_ne_top
  have hVU : V ≤ U := by
    apply ENNReal.coe_le_coe.mp
    rw [hVdef, hUdef, ENNReal.coe_toNNReal hfin, ENNReal.coe_toNNReal hround]
    exact le_roundUp Δ hΔ _
  have hUV : U - V ≤ Δ := by
    apply tsub_le_iff_left.mpr
    exact roundUp_toNNReal_le_add_step Δ hΔ _ hfin
  have hsplit : U = V + (U - V) := (add_tsub_cancel_of_le hVU).symm
  rw [hsplit, coordinateMaximum_add, coordinateMaximum_at_passage Δ lam R a γ i n hfin]
  apply max_le
  · exact le_add_of_nonneg_right (coordinateMaximum_nonneg _ i _)
  · exact add_le_add_right (coordinateMaximum_mono _ i hUV) _

/-- Each new passage lies at most one window maximum plus `R` above the previous one. -/
theorem passage_increment_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ) (hR : 0 < R)
    (γ : Path d) (i : Fin d) (n : ℕ)
    (hfin : passageSequence Δ lam R a γ i (n + 1) ≠ ⊤) :
    γ (passageSequence Δ lam R a γ i (n + 1)).toNNReal i -
        γ (passageSequence Δ lam R a γ i n).toNNReal i ≤
      coordinateMaximum
        (pathTimeShift γ (passageSequence Δ lam R a γ i n).toNNReal) i Δ + R := by
  obtain ⟨hround, hval⟩ := passage_displacement_succ Δ lam R a hR γ i n hfin
  have hnfin : passageSequence Δ lam R a γ i n ≠ ⊤ := by
    intro htop
    apply hround
    rw [htop, roundUp, ite_eq_left rfl]
  have hmax := coordinateMaximum_roundUp_passage_le Δ hΔ lam R a γ i n hnfin
  linarith

/-- A failed guard at a finite rounded passage moves the coordinate by more than
`R / 2` within one regeneration interval after the passage. -/
theorem window_escape_of_not_good {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) (n : ℕ)
    (hfin : passageSequence Δ lam R a γ i n ≠ ⊤)
    (hbad : ¬ IsGoodPassage Δ lam R a γ i n) :
    ∃ s : ℝ≥0, s ≤ Δ ∧ R / 2 <
      |pathTimeShift γ (passageSequence Δ lam R a γ i n).toNNReal s i -
        pathTimeShift γ (passageSequence Δ lam R a γ i n).toNNReal 0 i| := by
  have hround : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤ := by
    rw [roundUp, ite_eq_right hfin]
    exact ENNReal.coe_ne_top
  simp only [IsGoodPassage, not_and, not_forall, not_le] at hbad
  obtain ⟨u, hu, hlt⟩ := hbad hfin hround
  set V := (passageSequence Δ lam R a γ i n).toNNReal with hVdef
  refine ⟨u - V, ?_, ?_⟩
  · apply tsub_le_iff_left.mpr
    exact hu.2.trans (roundUp_toNNReal_le_add_step Δ hΔ _ hfin)
  · have hsum : V + (u - V) = u := add_tsub_cancel_of_le hu.1
    simpa only [pathTimeShift, ContinuousMap.coe_mk, add_zero, hsum] using hlt

/-- At a good passage the rounded time stays within `R / 2` of the passage. -/
theorem good_passage_roundUp_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) (n : ℕ) (hgood : IsGoodPassage Δ lam R a γ i n) :
    γ (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal i -
      γ (passageSequence Δ lam R a γ i n).toNNReal i ≤ R / 2 := by
  obtain ⟨hV, hU, hosc⟩ := hgood
  have hmem : (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal ∈
      Set.Icc (passageSequence Δ lam R a γ i n).toNNReal
        (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal := by
    refine ⟨?_, le_rfl⟩
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal hV, ENNReal.coe_toNNReal hU]
    exact le_roundUp Δ hΔ _
  exact (abs_le.mp (hosc _ hmem)).2

/-- Roundings of successive passages are nondecreasing. -/
theorem roundUp_passage_mono {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ) (hR : 0 < R)
    (γ : Path d) (i : Fin d) {m n : ℕ} (hmn : m ≤ n) :
    roundUp Δ (passageSequence Δ lam R a γ i m) ≤
      roundUp Δ (passageSequence Δ lam R a γ i n) := by
  have hV := monotone_passageSequence Δ hΔ lam R a hR γ i hmn
  by_cases htop : passageSequence Δ lam R a γ i n = ⊤
  · have htop' : roundUp Δ (passageSequence Δ lam R a γ i n) = ⊤ := by
      rw [htop]
      simp [roundUp]
    rw [htop']
    exact le_top
  · have hmtop : passageSequence Δ lam R a γ i m ≠ ⊤ := ne_top_of_le_ne_top htop hV
    rw [roundUp, ite_eq_right hmtop, roundUp, ite_eq_right htop]
    apply ENNReal.coe_le_coe.mpr
    apply mul_le_mul_of_nonneg_right _ zero_le
    apply Nat.cast_le.mpr
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ (NNReal.coe_nonneg Δ)
    exact ENNReal.toReal_mono htop hV

/-- The first rounded candidate is the rounding of the first good passage. -/
theorem firstRoundedCandidate_eq_first_good {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (γ : Path d) (i : Fin d)
    (hfin : firstRoundedCandidate Δ lam R a γ i ≠ ⊤) :
    ∃ k, IsGoodPassage Δ lam R a γ i k ∧ (∀ j < k, ¬ IsGoodPassage Δ lam R a γ i j) ∧
      firstRoundedCandidate Δ lam R a γ i = roundUp Δ (passageSequence Δ lam R a γ i k) := by
  classical
  have hex : ∃ n : ℕ, IsGoodPassage Δ lam R a γ i n := by
    by_contra hnone
    have hno : ∀ n : ℕ, ¬ IsGoodPassage Δ lam R a γ i n := not_exists.mp hnone
    apply hfin
    rw [firstRoundedCandidate]
    simp only [hno, iInf_of_empty, iInf_top]
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj, ?_⟩
  apply le_antisymm
  · exact iInf_le_of_le (Nat.find hex) (iInf_le_of_le (Nat.find_spec hex) le_rfl)
  · rw [firstRoundedCandidate]
    refine le_iInf fun m => le_iInf fun hm => ?_
    exact roundUp_passage_mono Δ hΔ lam R a hR γ i (Nat.find_min' hex hm)

end EinsteinFull.Regeneration
