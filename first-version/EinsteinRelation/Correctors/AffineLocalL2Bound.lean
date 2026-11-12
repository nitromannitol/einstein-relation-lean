import EinsteinRelation.Correctors.ScalarLocalBound

/-! Source: `paper/main.tex:735-739`. The affine coordinate has bounded local L² cost. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- On the radius-four ball, adjoining an affine coordinate changes a
scalar L² norm by a dimension-dependent additive constant only. -/
theorem sqrt_integral_affine_radius_four_le (d : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (u : Vec d → ℝ) (i : Fin d) (c : ℝ),
      MemLp (fun x => u x - c) 2 (volume.restrict (ball 0 4)) →
      MemLp (fun x => x i + u x - c) 2 (volume.restrict (ball 0 4)) →
      Real.sqrt (∫ x in ball 0 4, |x i + u x - c| ^ 2 ∂volume) ≤
        A * (1 + Real.sqrt (∫ x in ball 0 4, |u x - c| ^ 2 ∂volume)) := by
  let V := (8 : ℝ)^d
  let A := 4 + 4 * V
  refine ⟨A, by dsimp [A, V]; positivity, ?_⟩
  intro u i c hu hw
  have hsubset : ball (0 : Vec d) 4 ⊆ Metric.closedBall 0 4 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 4)]
    intro j
    rw [Real.dist_eq]
    exact (Regeneration.coordinate_abs_le_euclideanNorm (x - 0) j).trans hx.le
  have hfinite : volume (ball (0 : Vec d) 4) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : Vec d) 4).measure_ne_top
      (measure_mono hsubset)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 4)) :=
    isFiniteMeasure_restrict.mpr hfinite
  have hmass : volume.real (ball (0 : Vec d) 4) ≤ V := by
    have h := measureReal_mono (μ := (volume : Measure (Vec d))) hsubset
      (isCompact_closedBall (0 : Vec d) 4).measure_ne_top
    simpa only [V, measureReal_def, Real.volume_pi_closedBall _ (by norm_num : (0 : ℝ) ≤ 4),
      Fintype.card_fin, show (2 : ℝ) * 4 = 8 by norm_num,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 8 ^ d)] using h
  have hsq : Integrable (fun x => |u x - c|^2) (volume.restrict (ball 0 4)) := by
    simpa only [sq_abs] using hu.integrable_sq
  have hwaff : Integrable (fun x => |x i + u x - c|^2) (volume.restrict (ball 0 4)) := by
    simpa only [sq_abs] using hw.integrable_sq
  have hmeas : MeasurableSet (ball (0 : Vec d) 4) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hlarge : (∫ x in ball 0 4, |x i + u x - c|^2 ∂volume) ≤
      2 * (∫ x in ball 0 4, |u x - c|^2 ∂volume) + 32 * V := by
    calc
      _ ≤ ∫ x in ball 0 4, 2 * |u x - c|^2 + 32 ∂volume := by
        apply integral_mono_ae hwaff ((hsq.const_mul 2).add (integrable_const 32))
        filter_upwards [ae_restrict_mem hmeas] with x hx
        have hc4 : |x i| ≤ 4 := by
          simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using
            (Regeneration.coordinate_abs_le_euclideanNorm (x - 0) i).trans hx.le
        have hx2 : (x i)^2 ≤ 16 := by
          nlinarith only [sq_abs (x i), sq_nonneg (4 - |x i|), hc4, abs_nonneg (x i)]
        simp only [sq_abs, Pi.add_apply]
        nlinarith only [sq_nonneg (x i - (u x - c)), hx2]
      _ = 2 * (∫ x in ball 0 4, |u x - c|^2 ∂volume) +
          32 * volume.real (ball (0 : Vec d) 4) := by
        rw [integral_add (hsq.const_mul 2) (integrable_const 32), integral_const_mul]
        simp only [setIntegral_const, smul_eq_mul, mul_comm (volume.real _) 32]
      _ ≤ _ := by linarith only [hmass]
  apply (Real.sqrt_le_left (by dsimp [A, V]; positivity)).mpr
  have hI : 0 ≤ ∫ x in ball 0 4, |u x - c|^2 ∂volume :=
    integral_nonneg fun _ => sq_nonneg _
  have hs := Real.sq_sqrt hI
  have hs0 := Real.sqrt_nonneg (∫ x in ball 0 4, |u x - c|^2 ∂volume)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hA2 : 2 ≤ A^2 ∧ 32 * V ≤ A^2 := by
    dsimp [A]
    constructor <;> nlinarith only [hV, sq_nonneg V]
  nlinarith only [hlarge, hs, hs0, hA2.2,
    mul_nonneg (sub_nonneg.mpr hA2.1) hI, mul_nonneg (sq_nonneg A) hs0]

end EinsteinRelation.Correctors
