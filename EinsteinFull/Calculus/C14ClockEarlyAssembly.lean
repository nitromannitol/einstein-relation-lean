import EinsteinFull.Calculus.C14ClockEarlyUnforcedPropagation
import EinsteinFull.Calculus.C1ClockForcedEarlyDifference
import EinsteinFull.Calculus.C1ClockEarlyForceWindow
import EinsteinFull.Calculus.C5ClockHomogeneousTimeReplacement
import EinsteinFull.Calculus.S2ClockEarlyAssembly
import EinsteinFull.Calculus.C9ResponseThresholdEnergy
import EinsteinFull.Calculus.ComplexTransposeSupport
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_l2
import EinsteinFull.Blueprint.Foundation.node_e_u3A_centered_u2D_equations
import EinsteinFull.Blueprint.Roots.node_l_u3A_late_u2D_propagation

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem clock_early_constant_mono {C C' z T p b : ℝ}
    (hC : 0 ≤ C) (hCC : C ≤ C') (hz : 0 ≤ z) (hT : 0 ≤ T)
    (hp : 0 ≤ p) (hb : 0 ≤ b) :
    C * Real.exp (C * z * T) * p * b ≤
      C' * Real.exp (C' * z * T) * p * b := by
  apply mul_le_mul_of_nonneg_right _ hb
  apply mul_le_mul_of_nonneg_right _ hp
  exact mul_le_mul hCC (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hz) hT))
    (Real.exp_pos _).le (hC.trans hCC)

/-- The early clock comparison, with exactly the four source-graph dependencies. -/
theorem c14_clock_early_of_deps :
    node_e_u3A_clock_u2D_averageStmt →
    node_e_u3A_clock_u2D_l2Stmt →
    node_e_u3A_centered_u2D_equationsStmt →
    node_l_u3A_late_u2D_propagationStmt →
    node_e_u3A_clock_u2D_earlyStmt := by
  intro havg _hl2 _heq hlate d hd D
  obtain ⟨C1, t1, hC1, ht1, h1⟩ := clock_unforced_full_gaussian_smoothing havg d hd D
  obtain ⟨C2, t2, hC2, ht2, h2⟩ := clock_forced_early_difference havg d hd D
  obtain ⟨C3, hC3, h3⟩ := clock_homogeneous_time_replacement d hd D
  obtain ⟨C4, t4, hC4, ht4, h4⟩ := clock_unforced_early_propagation havg d hd D
  obtain ⟨gl, Cl, Tl, hgl, hCl, hTl, hl, hlw⟩ :=
    hlate d hd D (1 / 4) (by norm_num) (by norm_num)
  let gain := min gl (1 / 8)
  let t0 := max t1 (max t2 t4)
  have ht01 : t1 ≤ t0 := le_max_left _ _
  have ht02 : t2 ≤ t0 := (le_max_left _ _).trans (le_max_right _ _)
  have ht04 : t4 ≤ t0 := (le_max_right _ _).trans (le_max_right _ _)
  have ht0 : 1 ≤ t0 := ht1.trans ht01
  refine ⟨gain, C1, t0, lt_min hgl (by norm_num), hC1, ht0, ?_⟩
  intro C0 hC0
  obtain ⟨Clw, Tlw, hClw, hTlw, hlw⟩ := hlw C0 hC0
  obtain ⟨Tf, hTf, hf⟩ := clock_early_force_window t0 C0 ht0 hC0
  let CL := max Cl Clw
  let Cw := C2 + C4 + C3 + CL
  let T0 := max Tf (max Tl Tlw)
  have hCL : 0 < CL := hCl.trans_le (le_max_left _ _)
  have hCw : 0 < Cw := by dsimp only [Cw]; positivity
  have hC2w : C2 ≤ Cw := by dsimp only [Cw]; linarith
  have hC3w : C3 ≤ Cw := by dsimp only [Cw]; linarith
  have hC4w : C4 ≤ Cw := by dsimp only [Cw]; linarith
  have hTf0 : Tf ≤ T0 := le_max_left _ _
  have hTl0 : Tl ≤ T0 := (le_max_left _ _).trans (le_max_right _ _)
  have hTlw0 : Tlw ≤ T0 := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Cw, T0, hCw, (by linarith [hTf0]), ?_⟩
  intro Q hQ a μ ha hμ P hP
  dsimp only
  constructor
  · intro τ hτ s hs hτs
    exact h1 Q hQ a μ ha hμ (P 0) (hP 0) τ (ht01.trans hτ) s hs hτs
  intro T hT0 ζ hwindow
  let τ := T ^ (1 - (1 / 4 : ℝ))
  obtain ⟨hτ0, hτT, hforce⟩ := hf T (hTf0.trans hT0)
  have hT2 : 2 ≤ T := by linarith [hTf0, hTf]
  have hT1 : 1 < T := by linarith
  have hT : 0 < T := by linarith
  have hτ : 0 ≤ τ := Real.rpow_nonneg hT.le _
  have hτco : (τ.toNNReal : ℝ) = τ := Real.coe_toNNReal τ hτ
  have ht : 0 < T - τ := by
    have : 5 * τ ≤ T := hτT
    have : 0 < τ := Real.rpow_pos_of_pos hT _
    linarith
  have hτ2 : 2 * τ ≤ T := by
    have hτT' : 5 * τ ≤ T := hτT
    linarith only [hτT', hτ]
  have e2 := h2 Q hQ a μ ha hμ P hP T τ.toNNReal
    (by simpa only [hτco] using ht)
    (by rw [hτco]; exact ht02.trans hτ0)
    (by simpa only [hτco] using hτT) ζ
    (by simpa only [hτco] using hforce ζ hwindow)
  have e4 := h4 Q hQ a μ ha hμ P hP T τ.toNNReal
    (by simpa only [hτco] using ht)
    (by rw [hτco]; exact ht04.trans hτ0)
    (by simpa only [hτco] using hτT) ζ
  simp only [hτco] at e2 e4
  have e3 := h3 Q hQ μ hμ T τ hT ht hT2 hτ hτ2 ζ
  obtain ⟨_, _, hβex⟩ := response_reduced_drift_exists_uniform_bound d D
  obtain ⟨β, hβ, _⟩ := hβex Q hQ
  let Pdag := fun ζ t => complexL2Transpose (reducedLaw Q) (P ζ t)
  have hPdag (ζ : ℂ) : IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ) :=
    isComplexTransposeSemigroup_complexL2Transpose Q (P ζ)
  have eL :
      ‖clockEndpoint Q ζ (P ζ) μ T.toNNReal -
          homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht ζ
            (ζ • centeredComplexLp Q (P ζ τ.toNNReal μ))‖ ≤
        CL * Real.exp (CL * ‖ζ‖ ^ 2 * T) *
          T ^ (-(1 / 2 + (d : ℝ) / 4) - gl) := by
    rcases hwindow with hw | ⟨x, rfl, hw⟩
    · have hb := hl Q hQ β a μ hβ ha hμ T hT1 (hTl0.trans hT0) ζ hw
        (P ζ) (Pdag ζ) (hP ζ) (hPdag ζ) (.inr false)
      simp only [indexedEndpoint, endpointDriftSign, Complex.ofReal_one, one_mul,
        clockEndpoint] at hb
      refine hb.trans ?_
      simpa only [mul_one] using clock_early_constant_mono hCl.le (le_max_left Cl Clw)
        (sq_nonneg ‖ζ‖) hT.le (Real.rpow_nonneg hT.le
          (-(1 / 2 + (d : ℝ) / 4) - gl)) (show (0 : ℝ) ≤ 1 by norm_num)
    · have hb := hlw Q hQ β a μ hβ ha hμ T hT1 (hTlw0.trans hT0) x hw
        (P (x : ℂ)) (Pdag (x : ℂ)) (hP (x : ℂ)) (hPdag (x : ℂ)) (.inr false)
      simp only [indexedEndpoint, endpointDriftSign, Complex.ofReal_one, one_mul,
        clockEndpoint] at hb
      have hx : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [← hx] at hb
      refine hb.trans ?_
      simpa only [mul_one] using clock_early_constant_mono hClw.le (le_max_right Cl Clw)
        (sq_nonneg ‖(x : ℂ)‖) hT.le (Real.rpow_nonneg hT.le
          (-(1 / 2 + (d : ℝ) / 4) - gl)) (show (0 : ℝ) ≤ 1 by norm_num)
  refine ⟨hT, ht, hτ0, hτ2, e2.trans ?_, e4.trans ?_, e3.trans ?_, ?_⟩
  · exact clock_early_constant_mono hC2.le hC2w (sq_nonneg ‖ζ‖) hT.le
      (Real.rpow_nonneg hT.le _) (Real.sqrt_nonneg _)
  · exact clock_early_constant_mono hC4.le hC4w (sq_nonneg ‖ζ‖) hT.le
      (Real.rpow_nonneg hT.le _) (Real.sqrt_nonneg _)
  · exact clock_early_constant_mono hC3.le hC3w (sq_nonneg ‖ζ‖) hT.le
      (Real.rpow_nonneg hT.le _) (div_nonneg hτ hT.le)
  · let H := homogeneousAverageCLM Q ⟨0, by omega⟩ (T - τ) ht ζ
    let M := centeredComplexLp Q μ
    let W1 := centeredComplexLp Q (P ζ τ.toNNReal μ)
    let W0 := centeredComplexLp Q (P 0 τ.toNNReal μ)
    let U := clockEndpoint Q ζ (P ζ) μ T.toNNReal
    let Hm := homogeneousAverage Q ⟨0, by omega⟩ T hT ζ M
    have hdecomp := clock_error_decomposition Q H ζ U Hm W1 W0 M
    have hnorm : ‖U - ζ • Hm‖ ≤
        ‖ζ • H (W1 - W0)‖ + ‖ζ • H (W0 - M)‖ +
          ‖ζ • (H M - Hm)‖ + ‖U - H (ζ • W1)‖ := by
      rw [hdecomp]
      calc
        _ ≤ (‖U - H (ζ • W1)‖ + ‖ζ • H (W1 - W0)‖ + ‖ζ • H (W0 - M)‖) +
            ‖ζ • (H M - Hm)‖ := norm_add₄_le
        _ = _ := by ring
    exact hnorm.trans (sum_four_scale (by linarith) (sq_nonneg ‖ζ‖)
      hC2.le hC4.le hC3.le hCL.le rfl (min_le_left _ _) (min_le_right _ _)
      e2 e4 e3 eL)

end EinsteinFull.Blueprint
