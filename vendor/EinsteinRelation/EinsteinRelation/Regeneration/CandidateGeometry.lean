import EinsteinRelation.Regeneration.PassageHeight
import EinsteinRelation.Regeneration.ShiftedMaximum

open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-! # Actual rounded candidate geometry

Source `paper/main.tex:283–321,353–374`. The rounded candidate sequence `Ñ_j(a)` is the
unchanged actual construction. Each finite successor candidate is the first rounded
candidate of the time-shifted path at level `3 λ R`, which advances the endpoint by at
least `5R/2 ≥ 0`. A joint induction keeps the initial height `a/λ − R/2` and the
running-maximum slack `R` at every finite term. No `Γₙ` or trial geometry is assumed.
-/

namespace EinsteinRelation.Regeneration

/-- Division of the step level `3 λ R` by `λ` gives the level `3 R`, for nonzero `λ`. -/
private theorem three_lam_R_div_eq (lam R : ℝ) (hlam : lam ≠ 0) :
    3 * lam * R / lam = 3 * R := by
  rw [show 3 * lam * R = 3 * R * lam by ring, mul_div_assoc, div_self hlam, mul_one]

/-- One finite successor step. The shifted candidate's slack and height gain, together
with the previous slack and height, give the new slack and the retained height. -/
private theorem candidateStep_geometry {d : ℕ} (lam R a : ℝ) (hR : 0 ≤ R)
    (γ : Path d) (i : Fin d) (T F : ℝ≥0)
    (hslack : coordinateMaximum γ i T ≤ γ T i - γ 0 i + R)
    (hheight : a / lam - R / 2 ≤ γ T i - γ 0 i)
    (hFslack : coordinateMaximum (pathTimeShift γ T) i F ≤
      (pathTimeShift γ T) F i - (pathTimeShift γ T) 0 i + R)
    (hFheight : 3 * R - R / 2 ≤ (pathTimeShift γ T) F i - (pathTimeShift γ T) 0 i) :
    coordinateMaximum γ i (T + F) ≤ γ (T + F) i - γ 0 i + R ∧
      a / lam - R / 2 ≤ γ (T + F) i - γ 0 i := by
  have hval0 : (pathTimeShift γ T) 0 i = γ T i := by
    show γ (T + 0) i = γ T i
    rw [add_zero]
  have hvalF : (pathTimeShift γ T) F i = γ (T + F) i := rfl
  have hdisp : 0 ≤ γ (T + F) i - γ T i := by linarith
  have hmax := coordinateMaximum_add γ i T F
  refine ⟨?_, ?_⟩
  · rw [hmax]
    apply max_le
    · linarith
    · linarith
  · linarith

/-- Joint induction over the finite rounded candidate sequence. Every finite term keeps
the running-maximum slack `R` and the height `a / λ − R / 2`. -/
private theorem roundedCandidateSequence_geometry {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hlam : lam ≠ 0) (hR : 0 ≤ R) (z : CoupledSample d) (i : Fin d)
    (n : ℕ) :
    roundedCandidateSequence Δ lam R a z i n ≠ ⊤ →
      coordinateMaximum z.1 i (roundedCandidateSequence Δ lam R a z i n).toNNReal ≤
        z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal i - z.1 0 i + R ∧
      a / lam - R / 2 ≤ z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal i - z.1 0 i := by
  induction n with
  | zero =>
    intro hfin
    exact ⟨firstRoundedCandidate_maximum_slack Δ hΔ lam R a hR z.1 i hfin,
      firstRoundedCandidate_height_lower_bound Δ hΔ lam R a hR z.1 i hfin⟩
  | succ n ih =>
    intro hfin
    have hprev : roundedCandidateSequence Δ lam R a z i n ≠ ⊤ := by
      intro ht
      apply hfin
      rw [roundedCandidateSequence, if_pos ht]
    obtain ⟨hslack, hheight⟩ := ih hprev
    have hstepFin : firstRoundedCandidate Δ lam R (3 * lam * R)
        (pathTimeShift z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal) i ≠ ⊤ := by
      intro htop
      apply hfin
      rw [roundedCandidateSequence, if_neg hprev, htop, add_top]
    have hsucc : roundedCandidateSequence Δ lam R a z i (n + 1) =
        roundedCandidateSequence Δ lam R a z i n + firstRoundedCandidate Δ lam R (3 * lam * R)
          (pathTimeShift z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal) i := by
      rw [roundedCandidateSequence, if_neg hprev]
    have hFslack := firstRoundedCandidate_maximum_slack Δ hΔ lam R (3 * lam * R) hR
      (pathTimeShift z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal) i hstepFin
    have hFheight := firstRoundedCandidate_height_lower_bound Δ hΔ lam R (3 * lam * R) hR
      (pathTimeShift z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal) i hstepFin
    rw [three_lam_R_div_eq lam R hlam] at hFheight
    rw [hsucc, ENNReal.toNNReal_add hprev hstepFin]
    exact candidateStep_geometry lam R a hR z.1 i _ _ hslack hheight hFslack hFheight

/-- Source `Ñ_j(a)` running-maximum slack. At every finite rounded candidate, the actual
running coordinate maximum exceeds the displacement there by at most `R`. -/
theorem roundedCandidateSequence_maximum_slack {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hlam : lam ≠ 0) (hR : 0 ≤ R) (z : CoupledSample d) (i : Fin d)
    (n : ℕ) (hfin : roundedCandidateSequence Δ lam R a z i n ≠ ⊤) :
    coordinateMaximum z.1 i (roundedCandidateSequence Δ lam R a z i n).toNNReal ≤
      z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal i - z.1 0 i + R :=
  (roundedCandidateSequence_geometry Δ hΔ lam R a hlam hR z i n hfin).1

/-- Source `Ñ_j(a)` height. At every finite rounded candidate, the endpoint lies at least
`a / λ − R / 2` above the starting point. -/
theorem roundedCandidateSequence_height_lower_bound {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hlam : lam ≠ 0) (hR : 0 ≤ R) (z : CoupledSample d) (i : Fin d)
    (n : ℕ) (hfin : roundedCandidateSequence Δ lam R a z i n ≠ ⊤) :
    a / lam - R / 2 ≤
      z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal i - z.1 0 i :=
  (roundedCandidateSequence_geometry Δ hΔ lam R a hlam hR z i n hfin).2

end EinsteinRelation.Regeneration
