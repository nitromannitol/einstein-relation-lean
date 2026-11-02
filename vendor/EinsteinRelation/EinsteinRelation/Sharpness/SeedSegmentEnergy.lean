import EinsteinRelation.Sharpness.Fields
import EinsteinRelation.Sharpness.SeedField
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Segment energy of the canonical seed field

Source: `paper/main.tex:1212–1218` (the actual sharpness seed `h = ζ * tanh(K * W)`) and
`paper/main.tex:1261–1265` (the clock-rate constant `c = δ 𝔼[|∇ψ|² / (1 + ∂₁ψ)]`). The
deterministic segment bound proved here is the analytic input for a later expectation lower
bound on that constant; the expectation itself is not formalized in this file.

For a fixed actual sample `W` and a coordinate `i`, the segment function
`F t = seedField d W (t • unitVector i)` is `C^∞`, with derivative
`coordinateDerivative i (seedField d W) (t • unitVector i)` by the Fréchet chain rule.
The fundamental theorem of calculus on `[0, 5]` and the mean-square Cauchy–Schwarz bound
`(∫ g)^2 ≤ 5 ∫ g^2` give the energy estimate. It is deterministic for every sample: no
randomness, stationarity, ergodicity or gradient-positivity premise is used.
-/

open MeasureTheory

namespace EinsteinRelation

namespace Sharpness

/-- Mean-square Cauchy–Schwarz on `[0, 5]`: `(∫ g)^2 ≤ 5 ∫ g^2` for continuous `g`.
The pointwise bound `2 c g ≤ g^2 + c^2`, integrated at the mean `c = (∫ g) / 5`, gives it. -/
private theorem sq_intervalIntegral_le_five (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t in (0:ℝ)..5, g t) ^ 2 ≤ 5 * ∫ t in (0:ℝ)..5, g t ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ t in (0:ℝ)..5, g t) / 5 := ⟨_, rfl⟩
  have hgi : IntervalIntegrable g volume 0 5 := hg.intervalIntegrable 0 5
  have hg2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 5 :=
    (hg.pow 2).intervalIntegrable 0 5
  have hcc : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  have hmono : (∫ t in (0:ℝ)..5, 2 * c * g t) ≤ ∫ t in (0:ℝ)..5, (g t ^ 2 + c ^ 2) :=
    intervalIntegral.integral_mono_on (by norm_num) (hgi.const_mul (2 * c)) (hg2.add hcc)
      (fun t _ => show 2 * c * g t ≤ g t ^ 2 + c ^ 2 by nlinarith [sq_nonneg (g t - c)])
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hg2 hcc,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  subst hc
  nlinarith [hmono]

/-- Segment energy of the canonical seed field in coordinate `i`. Along the segment
`t ↦ t • unitVector i` on `[0, 5]`, the squared increment of the seed field is at most
`5` times the integrated squared coordinate derivative. -/
theorem seedField_segment_energy_le {d : ℕ} (W : NoiseSample d) (i : Fin d) :
    (seedField d W ((5 : ℝ) • unitVector i) - seedField d W 0) ^ 2 ≤
      5 * ∫ t : ℝ in (0)..5, (coordinateDerivative i (seedField d W) (t • unitVector i)) ^ 2 := by
  -- The coordinate segment `t ↦ t • e_i` has constant velocity `e_i`.
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • unitVector i) (unitVector i) t := by
    intro t
    have h := (hasDerivAt_id' (x := t)).smul_const (unitVector i)
    rwa [one_smul] at h
  -- The seed field is `C^∞`, hence Fréchet differentiable at every point.
  have hseed : ∀ t : ℝ, HasFDerivAt (seedField d W)
      (fderiv ℝ (seedField d W) (t • unitVector i)) (t • unitVector i) := fun t =>
    ((contDiff_seedField d W).differentiable (by simp) (t • unitVector i)).hasFDerivAt
  -- Chain rule: the restriction to the segment has derivative `∂ᵢ seed (t • e_i)`.
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => seedField d W (s • unitVector i))
      (coordinateDerivative i (seedField d W) (t • unitVector i)) t := fun t =>
    HasFDerivAt.comp_hasDerivAt (x := t) (hseed t) (hline t)
  -- The coordinate derivative is continuous, since the seed field is `C^∞`.
  have hcont_grad : Continuous (fun x : Vec d => coordinateDerivative i (seedField d W) x) := by
    unfold coordinateDerivative
    exact ((contDiff_seedField d W).continuous_fderiv (by simp)).clm_apply continuous_const
  have hsmul : Continuous (fun t : ℝ => t • unitVector i) :=
    continuous_id.smul continuous_const
  have hcont_line : Continuous
      (fun t : ℝ => coordinateDerivative i (seedField d W) (t • unitVector i)) :=
    hcont_grad.comp hsmul
  -- Fundamental theorem of calculus on `[0, 5]` along the segment.
  have hFTC : (∫ t in (0:ℝ)..5, coordinateDerivative i (seedField d W) (t • unitVector i)) =
      seedField d W ((5 : ℝ) • unitVector i) - seedField d W ((0 : ℝ) • unitVector i) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => seedField d W (s • unitVector i))
      (fun t _ => hderiv t) (hcont_line.intervalIntegrable 0 5)
  have hF0 : seedField d W ((0 : ℝ) • unitVector i) = seedField d W 0 := by
    simp
  rw [hF0] at hFTC
  rw [← hFTC]
  exact sq_intervalIntegral_le_five _ hcont_line

end Sharpness
end EinsteinRelation
