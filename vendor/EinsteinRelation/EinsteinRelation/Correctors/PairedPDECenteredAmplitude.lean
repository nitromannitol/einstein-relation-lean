import EinsteinRelation.Correctors.PairedPDEAmplitude

/-! # Centering the paired harmonic amplitude by a spatial kernel

Source: `paper/main.tex:862–873`. A nonnegative mass-one kernel supported
in the inner ball may replace the ball average in the oscillation estimate.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

/-- The actual centered value is bounded using the weak harmonic equation.
The kernel is arbitrary subject to positivity, mass one, and spatial support.
Source: `paper/main.tex:862–873`. -/
theorem paired_harmonic_centered_amplitude_of_gt
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {d : ℕ} (hd : 2 ≤ d) {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (a : Vec d → Mat d) (u : Vec d → ℝ) (G : Vec d → Vec d),
        EllipticBound (ball 0 (2 * R)) a lam Λ →
        WeakSolution (ball 0 (2 * R)) a u G →
        ContinuousOn u (ball 0 R) →
        ∀ (w : Vec d → ℝ), Integrable w volume →
          Integrable (fun x => w x * u x) volume →
          (∀ x, 0 ≤ w x) → (∫ x, w x) = 1 →
          Function.support w ⊆ ball 0 R →
          ∀ x₀ ∈ ball 0 R,
            |u x₀ - ∫ x, w x * u x| ≤
              C * R ^ (-(d : ℝ) / 2) * (2 * R) *
                Real.sqrt (∫ x in ball 0 (2 * R), euclideanSq (G x)) := by
  obtain ⟨CO, hCO, hO⟩ := paired_harmonic_ball_oscillation_of_gt h817 hP hd hlam hΛ
  refine ⟨2 * CO, mul_pos (by norm_num) hCO, ?_⟩
  intro R hR a u G hell hweak hcont w hw hwu hw0 hw1 hws x₀ hx₀
  let c := ⨍ y in ball 0 (2 * R), u y ∂volume
  let M := CO * R ^ (-(d : ℝ) / 2) * (2 * R) *
    Real.sqrt (∫ x in ball 0 (2 * R), euclideanSq (G x))
  have hbound : ∀ x ∈ ball 0 R, |u x - c| ≤ M := hO R hR a u G hell hweak hcont
  have heq : (∫ x, w x * (u x₀ - u x)) = u x₀ - ∫ x, w x * u x := by
    simp_rw [mul_sub]
    rw [integral_sub (hw.mul_const _) hwu, integral_mul_const, hw1, one_mul]
  have hle : ‖∫ x, w x * (u x₀ - u x)‖ ≤ 2 * M := by
    calc
      _ ≤ ∫ x, w x * (2 * M) := by
        apply norm_integral_le_of_norm_le (hw.mul_const _)
        exact ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 x)]
          by_cases hx : w x = 0
          · simp only [hx, zero_mul, le_refl]
          · apply mul_le_mul_of_nonneg_left _ (hw0 x)
            calc
              |u x₀ - u x| = |(u x₀ - c) - (u x - c)| := by congr 1; ring
              _ ≤ |u x₀ - c| + |u x - c| := abs_sub _ _
              _ ≤ M + M := add_le_add (hbound x₀ hx₀) (hbound x (hws hx))
              _ = 2 * M := by ring
      _ = 2 * M := by rw [integral_mul_const, hw1, one_mul]
  rw [heq, Real.norm_eq_abs] at hle
  convert hle using 1
  dsimp [M]
  ring

end EinsteinRelation.Correctors
