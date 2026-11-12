import EinsteinRelation.Correctors.PairedPDEAmplitude
import EinsteinRelation.External.AKMLocalCorrectors

/-! # Fixed-scale pointwise gradient estimate for the paired harmonic field

Source: `paper/main.tex:860–868`. This is the deterministic local step of
Step 3. The gradient is the actual continuous representative required by
GT 8.32. Its identification with a stationary corrector remains separate.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

/-- The fixed-scale gradient estimate, with a constant uniform over the
coefficient and solution. All regularity hypotheses of GT 8.32 are explicit.
Source: `paper/main.tex:860–868`; GT 8.32, (8.86), p. 210. -/
theorem paired_harmonic_gradient_origin_of_gt
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hP : BallPoincareEstimate) {d : ℕ} (hd : 2 ≤ d)
    {lam Λ K α : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λ)
    (hK : 0 < K) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → Mat d) (u : Vec d → ℝ)
      (G : Vec d → Vec d),
      EllipticBound (ball 0 1) a lam Λ →
      (∀ i j, HolderBound (ball 0 1) α (fun x => a x i j) K) →
      (∀ r : ℝ, 0 < r → r ≤ 1 → WeakSolution (ball 0 r) a u G) →
      C1Alpha (ball 0 1) α u G →
      euclideanNorm (G 0) ≤ C * vectorRms volume (ball 0 1) G := by
  obtain ⟨CO, hCO, hO⟩ := paired_harmonic_ball_oscillation_of_gt h817 hP hd hlam hΛ
  obtain ⟨CS, hCS, hS⟩ := h832 d hd lam K α (1/4) hlam hK hα hα1 (by norm_num)
  let F := CO * (1/2 : ℝ) ^ (-(d : ℝ) / 2)
  have hF : 0 < F := by dsimp [F]; positivity
  have hV := unitBall_volume_pos_finite d
  refine ⟨CS * F * Real.sqrt (volume.real (ball (0 : Vec d) 1)),
    mul_pos (mul_pos hCS hF) (Real.sqrt_pos.mpr hV), ?_⟩
  intro a u G hell hholder hweak hreg
  have hhalf : ball (0 : Vec d) (1/2 : ℝ) ⊆ ball 0 1 := by
    intro x hx
    exact lt_of_lt_of_le hx (by norm_num : (1/2 : ℝ) ≤ 1)
  let c := ⨍ y in ball 0 1, u y ∂volume
  have hcont : ContinuousOn u (ball (0 : Vec d) (1/2 : ℝ)) :=
    fun x hx => (hreg.1 x (hhalf hx)).continuousAt.continuousWithinAt
  have hosc := hO (1/2) (by norm_num) a u G
    (by simpa using hell) (by simpa using hweak 1 zero_lt_one le_rfl) hcont
  have hbound : ∀ x ∈ ball (0 : Vec d) (1/2 : ℝ),
      |u x - c| ≤ F * Real.sqrt (∫ y in ball 0 1, euclideanSq (G y)) := by
    simpa only [show 2 * (1/2 : ℝ) = 1 by norm_num, mul_one, F, c] using hosc
  have hfin := (ENNReal.toReal_pos_iff.mp (paired_ball_volume_pos_finite (d := d)
    (by norm_num : (0 : ℝ) < 1/2))).2.ne
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (1/2 : ℝ))) :=
    isFiniteMeasure_restrict.mpr hfin
  have hcweak := weakSolution_sub_const (hweak (1/2) (by norm_num) (by norm_num)) c
  have hcreg : C1Alpha (ball (0 : Vec d) (1/2 : ℝ)) α (fun x => u x - c) G := by
    refine ⟨fun x hx => ?_, ?_⟩
    · simpa only [sub_zero] using (hreg.1 x (hhalf hx)).sub_const c
    · obtain ⟨B, hB⟩ := hreg.2
      refine ⟨B, fun i => ?_⟩
      obtain ⟨S, H, hS, hH, hsum, hsup, hhold⟩ := hB i
      exact ⟨S, H, hS, hH, hsum, fun x hx => hsup x (hhalf hx),
        fun x hx y hy => hhold x (hhalf hx) y (hhalf hy)⟩
  have hscale : 2 * (1/4 : ℝ) = 1/2 := by norm_num
  have hgrad := hS a
    (by simpa only [show 2 * (1/4 : ℝ) = 1/2 by norm_num] using
      fun x (hx : x ∈ ball (0 : Vec d) (1/2 : ℝ)) => (hell.2 x (hhalf hx)).1)
    (by
      intro i j
      obtain ⟨S, H, hS, hH, hsum, hsup, hhold⟩ := hholder i j
      refine ⟨S, H, hS, hH, hsum, ?_, ?_⟩
      · intro x hx
        exact hsup x (hhalf (by simpa only [hscale] using hx))
      · intro x hx y hy
        exact hhold x (hhalf (by simpa only [hscale] using hx)) y (hhalf (by simpa only [hscale] using hy)))
    (fun x => u x - c) G (by simpa only [hscale] using hcweak) (by simpa only [hscale] using hcreg)
    (F * Real.sqrt (∫ y in ball 0 1, euclideanSq (G y))) (by positivity)
    (by simpa only [hscale] using hbound) 0 (by simp [ball, euclideanNorm, euclideanSq, dot])
  have hnorm : Real.sqrt (∫ y in ball (0 : Vec d) 1, euclideanSq (G y)) =
      Real.sqrt (volume.real (ball (0 : Vec d) 1)) * vectorRms volume (ball 0 1) G := by
    simp only [vectorRms, average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change Real.sqrt _ = Real.sqrt (volume.real (ball (0 : Vec d) 1)) *
      Real.sqrt ((volume.real (ball (0 : Vec d) 1))⁻¹ * _)
    rw [← Real.sqrt_mul hV.le, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]
  rw [hnorm] at hgrad
  convert hgrad using 1
  ring

end EinsteinRelation.Correctors
