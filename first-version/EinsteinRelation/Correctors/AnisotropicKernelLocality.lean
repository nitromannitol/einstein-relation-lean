import EinsteinRelation.Correctors.AnisotropicKernelWeakCalculus
import EinsteinRelation.Correctors.ScalarDecompositionLocality

/-! # A common observation window for anisotropic convolutions

Source: `paper/main.tex:1079–1084`. The uniform Euclidean bound on the
inverse coordinate map controls every band derivative and the final average
inside one observation ball, chosen before the environment law.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- All anisotropic band derivatives have the support window used in
Step 5 (`paper/main.tex:1079–1084`). -/
theorem measurable_localSigma_anisotropicBand_derivative (hd : 2 ≤ d)
    (B : Vec d ≃L[ℝ] Vec d) {L r S : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hB : ∀ x, euclideanNorm (B.symm x) ≤ L * euclideanNorm x)
    {f : FieldPair d → ℝ}
    (hf : Measurable[localSigma {x : Vec d | euclideanNorm x < S}] f)
    (cs : List (Fin d)) :
    Measurable[localSigma {x : Vec d | euclideanNorm x < S + 2 * L * r}]
      (horizontalMollify (coordinateIterate cs (anisotropicBandKernel B r)) f) :=
  measurable_localSigma_coordinateIterate_convolution (anisotropicBandKernel_contDiff hd B hr)
    (fun _ hx => anisotropicBandKernel_tail hd B hL hr hB hx) hf cs

/-- One common Euclidean ball contains every band observation window
(`paper/main.tex:1079–1084`). -/
theorem measurable_localSigma_anisotropicBand_common (hd : 2 ≤ d)
    (B : Vec d ≃L[ℝ] Vec d) {L r R : ℝ} (hL : 0 < L) (hr : 0 < r) (hrR : r ≤ R)
    (hB : ∀ x, euclideanNorm (B.symm x) ≤ L * euclideanNorm x)
    {f : FieldPair d → ℝ}
    (hf : Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * R}] f)
    (cs : List (Fin d)) :
    Measurable[localSigma {x : Vec d | euclideanNorm x < (33 + 2 * L) * R}]
      (horizontalMollify (coordinateIterate cs (anisotropicBandKernel B r)) f) := by
  apply (measurable_localSigma_anisotropicBand_derivative hd B hL hr hB hf cs).mono _ le_rfl
  apply Probability.localSigma_mono
  intro x hx
  change euclideanNorm x < (33 + 2 * L) * R
  change euclideanNorm x < 33 * R + 2 * L * r at hx
  nlinarith [mul_le_mul_of_nonneg_left hrR (show 0 ≤ 2 * L by positivity)]

/-- The largest-scale anisotropic average uses the same common window
(`paper/main.tex:1079–1084`). -/
theorem measurable_localSigma_anisotropicAverage_common
    (B : Vec d ≃L[ℝ] Vec d) {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hB : ∀ x, euclideanNorm (B.symm x) ≤ L * euclideanNorm x)
    {f : FieldPair d → ℝ}
    (hf : Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * R}] f) :
    Measurable[localSigma {x : Vec d | euclideanNorm x < (33 + 2 * L) * R}]
      (horizontalMollify (anisotropicAverage B R) f) := by
  have h := measurable_localSigma_coordinateIterate_convolution (anisotropicAverage_contDiff B hR)
    (fun _ hx => anisotropicAverage_tail B hL hR hB hx) hf []
  apply h.mono _ le_rfl
  apply Probability.localSigma_mono
  intro x hx
  change euclideanNorm x < (33 + 2 * L) * R
  change euclideanNorm x < 33 * R + L * R at hx
  nlinarith [mul_pos hL hR]

end EinsteinRelation.Correctors
