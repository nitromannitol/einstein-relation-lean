import EinsteinFull.Calculus.S2SmoothingBounds
import EinsteinFull.Blueprint.G3.Proofs.W4Queue0420_1

/-!
# Complex-force homogeneous averages are controlled by the averaging seminorm

The half-time splitting moves the complex force to the outer half-time Gaussian, whose operator
norm is `exp (K ‖ξ‖² s)`, and leaves the unforced half-time (derivative) average of the datum,
which is smoothed isotropically by `S2SmoothingBounds`.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

theorem norm_two_mul_sq (ξ : ℂ) : ‖(2 : ℂ) * ξ‖ ^ 2 = 4 * ‖ξ‖ ^ 2 := by
  rw [norm_mul, Complex.norm_two]
  ring

theorem norm_outer_half_le (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s) (ξ : ℂ)
    (g : Lp ℂ 2 (reducedLaw Q)) (hd : 2 ≤ d) :
    ‖homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ξ) g‖ ≤
      Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) * ‖g‖ := by
  have h := norm_homogeneousAverageCLM_le Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ξ)
  have e : sourceReducedBound Λ₀ * ‖(2 : ℂ) * ξ‖ ^ 2 * (s / 2) / 2 =
      sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s := by
    rw [norm_two_mul_sq]
    ring
  rw [e] at h
  calc _ = ‖homogeneousAverageCLM Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ξ) g‖ := rfl
    _ ≤ ‖homogeneousAverageCLM Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ξ)‖ * ‖g‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right h (norm_nonneg _)

theorem forced_average_le (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {s : ℝ} (hs : 0 < s)
    (hεs : 2 ≤ deconvEps Λ₀ * (s / 2)) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) {C : ℝ}
    (hC : 0 ≤ C) (hsem : gaussianAveragingSeminorm hd Q F ≤ ENNReal.ofReal C) (ξ : ℂ)
    (j : Fin d) :
    Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        ‖homogeneousAverage Q ⟨0, by omega⟩ s hs ξ (F j)‖ ≤
      Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) * C := by
  have hρ : 0 ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  rw [Blueprint.UnforcedIdentification.homogeneousAverage_half_split hd Q s hs ξ (F j)]
  have h1 := norm_outer_half_le Q s hs ξ (gaussianAverage hd Q (s / 2) (half_pos hs) (F j)) hd
  have h2 := norm_gaussianAverage_le_iso hd Q (half_pos hs) (F j)
  have h3 := iso_term_le hd Q hεs F hC hsem j
  calc _ ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        (Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) *
          ‖gaussianAverage hd Q (s / 2) (half_pos hs) (F j)‖) :=
      mul_le_mul_of_nonneg_left h1 hρ
    _ ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        (Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) *
          ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q (s / 2)) (F j)‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hρ
    _ = Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) *
        (Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
          ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q (s / 2)) (F j)‖) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le

theorem forced_derivative_le (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {s : ℝ} (hs : 0 < s)
    (hεs : 2 ≤ deconvEps Λ₀ * (s / 2)) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) {C : ℝ}
    (hC : 0 ≤ C) (hsem : gaussianAveragingSeminorm hd Q F ≤ ENNReal.ofReal C) (ξ : ℂ)
    (j i : Fin d) :
    Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ξ 1 (fun _ => i) (F j)‖ ≤
      Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) *
        (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) * C) := by
  have hρ : 0 ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hc : 0 ≤ Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) :=
    div_nonneg (Real.sqrt_nonneg _) (half_pos hs).le
  rw [Blueprint.UnforcedIdentification.homogeneousDerivativeAverage_half_split hd Q s hs ξ
    1 (by norm_num) (fun _ => i) (F j)]
  have h1 := norm_outer_half_le Q s hs ξ
    (gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) 1 (fun _ => i) (F j)) hd
  have h2 := norm_gaussianDerivativeAverage_le_iso hd Q (half_pos hs) (fun _ => i) (F j)
  have h3 := iso_term_le hd Q hεs F hC hsem j
  calc _ ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        (Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) *
          ‖gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) 1 (fun _ => i) (F j)‖) :=
      mul_le_mul_of_nonneg_left h1 hρ
    _ ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        (Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) *
          (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) *
            ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q (s / 2)) (F j)‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hρ
    _ = Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) *
        (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) *
          (Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
            ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q (s / 2))
              (F j)‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hc) (Real.exp_pos _).le

end EinsteinFull
