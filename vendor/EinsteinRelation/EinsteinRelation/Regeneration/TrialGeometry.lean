import EinsteinRelation.Regeneration.RegenerationGrid
import EinsteinRelation.Regeneration.Measurability
import EinsteinRelation.Occupation.FutureLocality
import EinsteinRelation.Regeneration.CandidateGeometry

/-! # All-trial prestart geometry of the actual regeneration construction

Source `paper/main.tex:365–374`. The prestart point of the `n`-th actual trial start is
`S_n - Δ`. A finite start has the form `S = F + N + Δ`, where `F` is the rounded failure
time of the previous trial and `N` is the first successful candidate of the time-shifted
path at the local level `a = λ (M(F) - (γ_F - γ_0) + R)`. A joint induction on the trial
index keeps the displacement at the prestart point at least `2R`. The running-maximum slack
`R` then follows from `coordinateMaximum_add` at the restart time `F`.

No `Γₙ` event, chronology, successful-bridge, or moment hypothesis is assumed.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- Division of the base level `3 λ R` by `λ` gives the level `3 R`, for nonzero `λ`. -/
private theorem trial_three_lam_R_div (lam R : ℝ) (hlam : lam ≠ 0) :
    3 * lam * R / lam = 3 * R := by
  rw [show 3 * lam * R = 3 * R * lam by ring, mul_div_assoc, div_self hlam, mul_one]

/-- A finite successful candidate at level `a` has running-maximum slack `R` and height at
least `a / λ - R / 2`. The attained grid representative supplies both bounds. -/
private theorem trial_successful_candidate_geometry {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hlam : lam ≠ 0) (hR : 0 ≤ R) (z : CoupledSample d) (i : Fin d)
    (hfin : firstSuccessfulCandidate Δ lam R a z i ≠ ⊤) :
    coordinateMaximum z.1 i (firstSuccessfulCandidate Δ lam R a z i).toNNReal ≤
      z.1 (firstSuccessfulCandidate Δ lam R a z i).toNNReal i - z.1 0 i + R ∧
    a / lam - R / 2 ≤ z.1 (firstSuccessfulCandidate Δ lam R a z i).toNNReal i - z.1 0 i := by
  obtain ⟨n, _, heq⟩ := firstSuccessfulCandidate_attained Δ hΔ lam R a z i hfin
  have hn : roundedCandidateSequence Δ lam R a z i n ≠ ⊤ := by
    rw [← heq]
    exact hfin
  rw [heq]
  exact ⟨roundedCandidateSequence_maximum_slack Δ hΔ lam R a hlam hR z i n hn,
    roundedCandidateSequence_height_lower_bound Δ hΔ lam R a hlam hR z i n hn⟩

/-- Real bookkeeping for one successor trial. The restart maximum `M(T)` lies at most `R/2`
below the new endpoint, because the local height gain is `M(T) - disp(T) + R/2`. The local
slack then transfers to the new endpoint through `coordinateMaximum_add`. -/
private theorem trial_successor_prestart_geometry {d : ℕ} (γ : Path d) (i : Fin d)
    (T L : ℝ≥0) (R : ℝ) (hR : 0 < R) (hB : 2 * R ≤ coordinateMaximum γ i T)
    (hgain : coordinateMaximum γ i T - (γ T i - γ 0 i) + R - R / 2 ≤ γ (T + L) i - γ T i)
    (hslack : coordinateMaximum (pathTimeShift γ T) i L ≤ γ (T + L) i - γ T i + R) :
    coordinateMaximum γ i (T + L) ≤ γ (T + L) i - γ 0 i + R ∧
      2 * R ≤ γ (T + L) i - γ 0 i := by
  rw [coordinateMaximum_add γ i T L]
  refine ⟨max_le ?_ ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- Joint induction on the trial index. A finite actual trial start has its prestart point
with running-maximum slack `R` and coordinate displacement at least `2R`. -/
private theorem trial_prestart_geometry {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (z : CoupledSample d) (i : Fin d) (n : ℕ) :
    trialStartSequence Δ lam R z i n ≠ ⊤ →
      coordinateMaximum z.1 i ((trialStartSequence Δ lam R z i n).toNNReal - Δ) ≤
        z.1 ((trialStartSequence Δ lam R z i n).toNNReal - Δ) i - z.1 0 i + R ∧
      2 * R ≤ z.1 ((trialStartSequence Δ lam R z i n).toNNReal - Δ) i - z.1 0 i := by
  induction n with
  | zero =>
    intro hfin
    have hform0 : trialStartSequence Δ lam R z i 0 =
        firstSuccessfulCandidate Δ lam R (3 * lam * R) z i + (Δ : ℝ≥0∞) := by
      rw [trialStartSequence]
    have hN0 : firstSuccessfulCandidate Δ lam R (3 * lam * R) z i ≠ ⊤ := by
      intro h
      apply hfin
      rw [hform0, h, top_add]
    have hP0 : (trialStartSequence Δ lam R z i 0).toNNReal - Δ =
        (firstSuccessfulCandidate Δ lam R (3 * lam * R) z i).toNNReal := by
      rw [hform0, ENNReal.toNNReal_add hN0 ENNReal.coe_ne_top, ENNReal.toNNReal_coe,
        add_tsub_cancel_right]
    obtain ⟨hslack, hheight⟩ := trial_successful_candidate_geometry Δ hΔ lam R (3 * lam * R)
      hlam.ne' hR.le z i hN0
    rw [trial_three_lam_R_div lam R hlam.ne'] at hheight
    rw [hP0]
    exact ⟨hslack, by linarith⟩
  | succ n ih =>
    intro hfin
    let t := trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n)
    have ht : t ≠ ⊤ := by
      intro h
      apply hfin
      change (if t = ⊤ then ⊤ else _) = ⊤
      rw [if_pos h]
    let a := lam * (coordinateMaximum z.1 i t.toNNReal -
      (z.1 t.toNNReal i - z.1 0 i) + R)
    have hform : trialStartSequence Δ lam R z i (n + 1) =
        t + firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i + Δ := by
      change (if t = ⊤ then ⊤ else _) = _
      rw [if_neg ht]
    -- The previous start is finite, since an infinite start has an infinite failure time.
    have hS : trialStartSequence Δ lam R z i n ≠ ⊤ := by
      intro h
      apply ht
      change trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n) = ⊤
      rw [trialFailureTime, trialDownwardTime, if_pos h, roundUp, if_pos rfl]
    -- The previous start is at most its failure time, hence the prestart point is too.
    have hSJ : trialStartSequence Δ lam R z i n ≤
        trialDownwardTime Δ R z i (trialStartSequence Δ lam R z i n) := by
      rw [trialDownwardTime, if_neg hS]
      exact le_add_of_nonneg_right zero_le
    have hSt : trialStartSequence Δ lam R z i n ≤ t := hSJ.trans (le_roundUp Δ hΔ _)
    have hSt' : (trialStartSequence Δ lam R z i n).toNNReal ≤ t.toNNReal :=
      (ENNReal.toNNReal_le_toNNReal hS ht).mpr hSt
    have hPT : (trialStartSequence Δ lam R z i n).toNNReal - Δ ≤ t.toNNReal :=
      le_trans tsub_le_self hSt'
    -- The past maximum at the restart time dominates the previous prestart displacement.
    have hB : 2 * R ≤ coordinateMaximum z.1 i t.toNNReal :=
      (ih hS).2.trans (displacement_le_coordinateMaximum z.1 i _ _ hPT)
    have hN : firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i ≠ ⊤ := by
      intro h
      apply hfin
      rw [hform, h, add_top, top_add]
    have hP : (trialStartSequence Δ lam R z i (n + 1)).toNNReal - Δ =
        t.toNNReal +
          (firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i).toNNReal := by
      rw [hform, ENNReal.toNNReal_add (ENNReal.add_ne_top.mpr ⟨ht, hN⟩) ENNReal.coe_ne_top,
        ENNReal.toNNReal_add ht hN, ENNReal.toNNReal_coe, add_tsub_cancel_right]
    -- The local successful candidate has slack `R` and height `a / λ - R / 2` on the shift.
    have hloc := trial_successful_candidate_geometry Δ hΔ lam R a hlam.ne' hR.le
      (sampleTimeShift Δ z t.toNNReal) i hN
    have h0 : (sampleTimeShift Δ z t.toNNReal).1 0 i = z.1 t.toNNReal i := by
      show z.1 (t.toNNReal + 0) i = z.1 t.toNNReal i
      rw [add_zero]
    rw [h0] at hloc
    have ha : a / lam = coordinateMaximum z.1 i t.toNNReal -
        (z.1 t.toNNReal i - z.1 0 i) + R := by
      show lam * (coordinateMaximum z.1 i t.toNNReal -
        (z.1 t.toNNReal i - z.1 0 i) + R) / lam = _
      exact mul_div_cancel_left₀ _ hlam.ne'
    have hgain : coordinateMaximum z.1 i t.toNNReal - (z.1 t.toNNReal i - z.1 0 i) + R - R / 2 ≤
        z.1 (t.toNNReal +
          (firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i).toNNReal) i -
          z.1 t.toNNReal i := by
      have h := hloc.2
      rw [ha] at h
      exact h
    have hslack : coordinateMaximum (pathTimeShift z.1 t.toNNReal) i
        (firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i).toNNReal ≤
        z.1 (t.toNNReal +
          (firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i).toNNReal) i -
          z.1 t.toNNReal i + R :=
      hloc.1
    rw [hP]
    exact trial_successor_prestart_geometry z.1 i t.toNNReal
      (firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i).toNNReal R hR hB
      hgain hslack

/-- Source `paper/main.tex:365–374`. At every finite actual trial start, the running coordinate
maximum at the prestart point `S - Δ` exceeds the displacement there by at most `R`. -/
theorem trial_prestart_maximum_slack {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (z : CoupledSample d) (i : Fin d) (n : ℕ)
    (hfin : trialStartSequence Δ lam R z i n ≠ ⊤) :
    coordinateMaximum z.1 i ((trialStartSequence Δ lam R z i n).toNNReal - Δ) ≤
      z.1 ((trialStartSequence Δ lam R z i n).toNNReal - Δ) i - z.1 0 i + R :=
  (trial_prestart_geometry Δ hΔ lam R hlam hR z i n hfin).1

/-- Source `paper/main.tex:365–374`. At every finite actual trial start, the prestart point
`S - Δ` lies at least `2R` above the starting point in the coordinate `i`. -/
theorem trial_prestart_height_lower_bound {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (z : CoupledSample d) (i : Fin d) (n : ℕ)
    (hfin : trialStartSequence Δ lam R z i n ≠ ⊤) :
    2 * R ≤ z.1 ((trialStartSequence Δ lam R z i n).toNNReal - Δ) i - z.1 0 i :=
  (trial_prestart_geometry Δ hΔ lam R hlam hR z i n hfin).2

end EinsteinRelation.Regeneration
