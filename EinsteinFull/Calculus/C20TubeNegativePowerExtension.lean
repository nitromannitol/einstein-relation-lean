import EinsteinFull.Calculus.C16TubeWeightedLogEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus
noncomputable section

/-- The negative power `(c16LogArgument ε x) ^ (-p)` of the regularized logarithmic argument. -/
def c20NegativePower (ε p x : ℝ) : ℝ := Real.rpow (c16LogArgument ε x) (-p)

theorem c20_negative_power_smooth {ε p : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (c20NegativePower ε p) := by
  exact c16_log_argument_contDiff.rpow_const_of_ne
    (fun x => (c16_log_argument_pos hε x).ne')

theorem c20_negative_power_eq {ε p x : ℝ} (hε : 0 < ε) (hx : 3 * ε / 4 ≤ x) :
    c20NegativePower ε p x = Real.rpow x (-p) := by
  simp only [c20NegativePower, c16_log_argument_eq hε hx]

theorem c20_negative_power_deriv {ε p x : ℝ} (hε : 0 < ε) (hx : 3 * ε / 4 < x) :
    deriv (c20NegativePower ε p) x = -p * Real.rpow x (-p-1) := by
  have hloc : c20NegativePower ε p =ᶠ[𝓝 x] (fun y => Real.rpow y (-p)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact c20_negative_power_eq hε (le_of_lt hy)
  rw [hloc.deriv_eq]
  simpa only [Real.rpow_eq_pow] using Real.deriv_rpow_const x (-p)

theorem c20_negative_power_second_deriv {ε p x : ℝ} (hε : 0 < ε)
    (hx : ε ≤ x) :
    deriv (deriv (c20NegativePower ε p)) x = p*(p+1)*Real.rpow x (-p-2) := by
  have hloc : deriv (c20NegativePower ε p) =ᶠ[𝓝 x]
      (fun y => -p * Real.rpow y (-p-1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show 3 * ε / 4 < x by linarith)] with y hy
    exact c20_negative_power_deriv hε hy
  rw [hloc.deriv_eq, deriv_const_mul_field]
  simp only [Real.rpow_eq_pow, Real.deriv_rpow_const]
  have he : -p - 1 - 1 = -p - 2 := by ring
  rw [he]
  ring

theorem c20_negative_power_deriv_zero {ε p x : ℝ} (hε : 0 < ε) (hx : x < ε / 2) :
    deriv (c20NegativePower ε p) x = 0 := by
  have hloc : c20NegativePower ε p =ᶠ[𝓝 x] (fun _ => Real.rpow (ε / 2) (-p)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    have hy' : y < ε / 2 := hy
    have ht : 4 * y / ε - 2 ≤ 0 := by
      have hh : 4 * y / ε ≤ 2 := (div_le_iff₀ hε).2 (by nlinarith)
      linarith
    simp only [c20NegativePower, c16LogArgument, Real.smoothTransition.zero_of_nonpos ht,
      zero_mul, add_zero]
  rw [hloc.deriv_eq, deriv_const]

theorem c20_negative_power_second_deriv_zero {ε p x : ℝ} (hε : 0 < ε)
    (hx : x < ε / 2) : deriv (deriv (c20NegativePower ε p)) x = 0 := by
  have hloc : deriv (c20NegativePower ε p) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact c20_negative_power_deriv_zero hε hy
  rw [hloc.deriv_eq, deriv_const]

theorem c20_negative_power_bounded {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv (c20NegativePower ε p) x| ≤ M ∧
      |deriv (deriv (c20NegativePower ε p)) x| ≤ M := by
  have h2 : ContDiff ℝ 2 (c20NegativePower ε p) :=
    (c20_negative_power_smooth hε).of_le (by simp)
  have hc1 : Continuous (fun x => |deriv (c20NegativePower ε p) x|) :=
    (h2.continuous_deriv (by simp)).abs
  have hc2 : Continuous (fun x => |deriv (deriv (c20NegativePower ε p)) x|) :=
    h2.deriv'.continuous_deriv_one.abs
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc : IsCompact (Set.Icc (ε / 2) ε)).bddAbove_image hc1.continuousOn
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc : IsCompact (Set.Icc (ε / 2) ε)).bddAbove_image hc2.continuousOn
  let C₁ := p * Real.rpow ε (-p-1)
  let C₂ := p * (p+1) * Real.rpow ε (-p-2)
  let M := max (max B₁ B₂) (max (max C₁ C₂) 0)
  have hM : 0 ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hb1 : B₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb2 : B₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc1' : C₁ ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hc2' : C₂ ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  refine ⟨M, hM, fun x => ?_⟩
  by_cases hlo : x < ε / 2
  · simp only [c20_negative_power_deriv_zero hε hlo,
      c20_negative_power_second_deriv_zero hε hlo, abs_zero, hM, and_self]
  by_cases hhi : ε ≤ x
  · have hx : 0 < x := lt_of_lt_of_le hε hhi
    have hr1 : Real.rpow x (-p-1) ≤ Real.rpow ε (-p-1) :=
      Real.rpow_le_rpow_of_nonpos hε hhi (by linarith)
    have hr2 : Real.rpow x (-p-2) ≤ Real.rpow ε (-p-2) :=
      Real.rpow_le_rpow_of_nonpos hε hhi (by linarith)
    constructor
    · rw [c20_negative_power_deriv hε (by linarith : 3 * ε / 4 < x)]
      simp only [Real.rpow_eq_pow] at *
      rw [abs_mul,
        abs_neg, abs_of_pos hp, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
      exact le_trans (mul_le_mul_of_nonneg_left hr1 hp.le) hc1'
    · rw [c20_negative_power_second_deriv hε hhi]
      simp only [Real.rpow_eq_pow] at *
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hp.le (by linarith)) (Real.rpow_nonneg hx.le _))]
      exact le_trans (mul_le_mul_of_nonneg_left hr2 (mul_nonneg hp.le (by linarith))) hc2'
  · exact ⟨le_trans (hB₁ ⟨x, ⟨le_of_not_gt hlo, le_of_not_ge hhi⟩, rfl⟩) hb1,
      le_trans (hB₂ ⟨x, ⟨le_of_not_gt hlo, le_of_not_ge hhi⟩, rfl⟩) hb2⟩

theorem c20_negative_power_normalized_extension
 (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) :
 ∃ F : ℝ → ℝ, ∃ c M : ℝ,
 ContDiff ℝ 2 F ∧ F 0 = 0 ∧ 0 ≤ M ∧
 (∀ x, |deriv F x| ≤ M ∧ |deriv (deriv F) x| ≤ M) ∧
 (∀ x, ε ≤ x → F x = Real.rpow x (-p) - c) ∧
 (∀ x, ε ≤ x → deriv F x = -p * Real.rpow x (-p-1)) ∧
 (∀ x, ε ≤ x → deriv (deriv F) x = p*(p+1)*Real.rpow x (-p-2)) := by
  obtain ⟨M, hM, hb⟩ := c20_negative_power_bounded hε hp
  let F : ℝ → ℝ := fun x => c20NegativePower ε p x - c20NegativePower ε p 0
  have hd : deriv F = deriv (c20NegativePower ε p) := deriv_sub_const_fun _
  refine ⟨F, c20NegativePower ε p 0, M, ?_, ?_, hM, ?_, ?_, ?_, ?_⟩
  · exact ((c20_negative_power_smooth hε).of_le (by simp)).sub contDiff_const
  · simp [F]
  · intro x; rw [hd]; exact hb x
  · intro x hx; simp only [F, c20_negative_power_eq hε (by linarith : 3 * ε / 4 ≤ x)]
  · intro x hx; rw [hd]; exact c20_negative_power_deriv hε (by linarith)
  · intro x hx; rw [hd]; exact c20_negative_power_second_deriv hε hx

end
end EinsteinFull.Calculus
