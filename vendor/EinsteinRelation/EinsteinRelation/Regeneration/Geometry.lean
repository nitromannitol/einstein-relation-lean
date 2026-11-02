import EinsteinRelation.Regeneration.Chronology

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-! # Actual good-passage running-maximum geometry

Source `paper/main.tex:283–322,365–374`. Actual construction definitions remain unchanged.
-/

namespace EinsteinRelation.Regeneration


theorem firstHittingAbove_le_iff {d : ℕ} (γ : Path d) (i : Fin d) (a : ℝ) (T : ℝ≥0) :
    firstHittingAbove γ i a ≤ (T : ℝ≥0∞) ↔
      ∃ t ∈ Set.Icc (0 : ℝ≥0) T, a ≤ γ t i - γ 0 i := by
  have hiff : ∀ t : ℝ≥0, (a ≤ γ t i - γ 0 i ↔ (-γ) t i - (-γ) 0 i ≤ -a) := by
    intro t
    simp only [ContinuousMap.neg_apply, Pi.neg_apply]
    constructor <;> intro h <;> linarith
  have heq : firstHittingAbove γ i a =
      ⨅ (t : ℝ≥0) (_ : (-γ) t i - (-γ) 0 i ≤ -a), (t : ℝ≥0∞) := by
    rw [firstHittingAbove]
    exact iInf_congr fun t => iInf_congr_Prop (hiff t) fun _ => rfl
  rw [heq, Probability.downcrossing_inf_le_iff (-γ) i (-a) T]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (hiff t).mpr h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (hiff t).mp h⟩

theorem coordinate_le_at_firstHittingAbove {d : ℕ} (γ : Path d) (i : Fin d)
    (a : ℝ) (V : ℝ≥0) (hV : firstHittingAbove γ i a = (V : ℝ≥0∞)) :
    ∀ s : ℝ≥0, s ≤ V → γ s i ≤ γ V i := by
  obtain ⟨u, hu, hcross⟩ := (firstHittingAbove_le_iff γ i a V).mp hV.le
  have htime := firstHittingAbove_le_of_crossing γ i a u hcross
  rw [hV] at htime
  have hVu : V ≤ u := ENNReal.coe_le_coe.mp htime
  have huV : u = V := le_antisymm hu.2 hVu
  have hcrossV : a ≤ γ V i - γ 0 i := by simpa only [huV] using hcross
  intro s hs
  by_cases hseq : s = V
  · subst s
    exact le_rfl
  · have hslt : s < V := lt_of_le_of_ne hs hseq
    by_contra hbad
    have hcrossS : a ≤ γ s i - γ 0 i := by linarith [lt_of_not_ge hbad]
    have htimeS := firstHittingAbove_le_of_crossing γ i a s hcrossS
    rw [hV] at htimeS
    exact (not_le_of_gt hslt) (ENNReal.coe_le_coe.mp htimeS)

theorem maximum_slack_of_good_hitting_interval {d : ℕ} (γ : Path d) (i : Fin d)
    (a : ℝ) (V U : ℝ≥0) (R : ℝ) (hR : 0 ≤ R)
    (hV : firstHittingAbove γ i a = (V : ℝ≥0∞)) (hVU : V ≤ U)
    (hosc : ∀ s ∈ Set.Icc V U, |γ s i - γ V i| ≤ R / 2) :
    coordinateMaximum γ i U ≤ γ U i - γ 0 i + R := by
  have hU := abs_le.mp (hosc U ⟨hVU, le_rfl⟩)
  apply coordinateMaximum_le
  intro s hs
  by_cases hsV : s ≤ V
  · have hbefore := coordinate_le_at_firstHittingAbove γ i a V hV s hsV
    linarith
  · have hinside := abs_le.mp (hosc s ⟨le_of_not_ge hsV, hs.2⟩)
    linarith

theorem goodPassage_maximum_slack {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 ≤ R) (γ : Path d) (i : Fin d) (n : ℕ)
    (hgood : IsGoodPassage Δ lam R a γ i n) :
    coordinateMaximum γ i (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal ≤
      γ (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal i - γ 0 i + R := by
  have hfinite : passageSequence Δ lam R a γ i n ≠ ⊤ := hgood.1
  have hroundfinite : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤ := hgood.2.1
  have hex : ∃ b : ℝ, passageSequence Δ lam R a γ i n = firstHittingAbove γ i b := by
    cases n with
    | zero => exact ⟨a / lam, by rw [passageSequence]⟩
    | succ m =>
        by_cases ht : roundUp Δ (passageSequence Δ lam R a γ i m) = ⊤
        · have heq : passageSequence Δ lam R a γ i (m + 1) = ⊤ := by
            rw [passageSequence, if_pos ht]
          exact False.elim (hfinite heq)
        · refine ⟨coordinateMaximum γ i
            (roundUp Δ (passageSequence Δ lam R a γ i m)).toNNReal + R, ?_⟩
          rw [passageSequence, if_neg ht]
  obtain ⟨b, hb⟩ := hex
  have hfirst : firstHittingAbove γ i b =
      ((passageSequence Δ lam R a γ i n).toNNReal : ℝ≥0∞) :=
    hb.symm.trans (ENNReal.coe_toNNReal hfinite).symm
  have hle : (passageSequence Δ lam R a γ i n).toNNReal ≤
      (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_toNNReal hfinite, ENNReal.coe_toNNReal hroundfinite] using
      le_roundUp Δ hΔ (passageSequence Δ lam R a γ i n)
  exact maximum_slack_of_good_hitting_interval γ i b _ _ R hR hfirst hle hgood.2.2

theorem firstRoundedCandidate_maximum_slack {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 ≤ R) (γ : Path d) (i : Fin d)
    (hfinite : firstRoundedCandidate Δ lam R a γ i ≠ ⊤) :
    coordinateMaximum γ i (firstRoundedCandidate Δ lam R a γ i).toNNReal ≤
      γ (firstRoundedCandidate Δ lam R a γ i).toNNReal i - γ 0 i + R := by
  have hex : ∃ n : ℕ, IsGoodPassage Δ lam R a γ i n := by
    by_contra hnone
    have hno : ∀ n : ℕ, ¬ IsGoodPassage Δ lam R a γ i n := not_exists.mp hnone
    have htop : firstRoundedCandidate Δ lam R a γ i = ⊤ := by
      rw [firstRoundedCandidate]
      simp only [hno, iInf_of_empty, iInf_top]
    exact hfinite htop
  obtain ⟨n, hn, htime⟩ := firstRoundedCandidate_attained Δ hΔ lam R a γ i hex
  have hbound := goodPassage_maximum_slack Δ hΔ lam R a hR γ i n hn
  rw [← htime] at hbound
  exact hbound

end EinsteinRelation.Regeneration
