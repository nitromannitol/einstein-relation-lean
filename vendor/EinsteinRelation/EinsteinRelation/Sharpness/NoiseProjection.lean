import EinsteinRelation.Sharpness.NoiseOrthogonality
import EinsteinRelation.Sharpness.NoiseVariance
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Ring

/-! # Orthogonal projection of compact-test noise evaluations

Source: `paper/main.tex:1212–1216`, the internal finite-range construction
`h ≔ ζ * tanh(K * W)` in the proof of `sharp.example` (Proposition 7.1). The generic
white-noise law `hwhite` is an explicit hypothesis here, as in `NoiseOrthogonality`.

For a nonzero actual compact test `f`, the residual `g - (∫ f g / ∫ f²) • f` has zero
integral covariance with `f`. Its evaluation is then independent of `W f`, by
`indepFun_noise_evaluations_of_orthogonal`. This is a test-level projection statement. It is
not σ-algebra independence of all residual observations, and it assumes no nondegeneracy
of `h`; both remain internal obligations.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The product of two compact smooth tests is integrable on coordinate space. -/
private theorem noiseTest_mul_integrable {d : ℕ} (f g : NoiseTest d) :
    Integrable (fun y : Vec d => f y * g y) := by
  have hfg : HasCompactSupport ((f : Vec d → ℝ) * (g : Vec d → ℝ)) :=
    f.hasCompactSupport.mul_right
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (f.contDiff.continuous).mul (g.contDiff.continuous)
  · exact hfg

/-- Pointwise value of a difference of a test and a scalar multiple of another test. -/
private theorem noiseTest_sub_smul_apply {d : ℕ} (g f : NoiseTest d) (c : ℝ) (y : Vec d) :
    (g - c • f) y = g y - c * f y :=
  rfl

/-- Expansion of `f * (g - c • f)` under the integral, with both pieces integrable. -/
private theorem integral_noiseTest_mul_sub_smul {d : ℕ} (f g : NoiseTest d) (c : ℝ) :
    (∫ y : Vec d, f y * (g - c • f) y) =
      (∫ y : Vec d, f y * g y) - c * (∫ y : Vec d, (f y) ^ 2) := by
  have hpt : ∀ y : Vec d, f y * (g - c • f) y = f y * g y - c * (f y) ^ 2 := by
    intro y
    rw [noiseTest_sub_smul_apply]
    ring
  simp_rw [hpt]
  rw [integral_sub (noiseTest_mul_integrable f g) ((noiseTest_sq_integrable f).const_mul c),
    integral_const_mul]

/-- The residual of the `L²` projection of `g` onto `f` is orthogonal to `f`. -/
theorem integral_noiseTest_projection_orthogonal {d : ℕ} (f g : NoiseTest d) (hf : f ≠ 0) :
  (∫ y : Vec d, f y * (g - (((∫ z : Vec d, f z * g z) /
    (∫ z : Vec d, (f z)^2))) • f) y) = 0 := by
  have hD : (∫ z : Vec d, (f z)^2) ≠ 0 := (noiseTest_l2_mass_pos f hf).ne'
  rw [integral_noiseTest_mul_sub_smul, div_mul_cancel₀ _ hD, sub_self]

/-- A test `f` equal to `1` on the support of `g` leaves `∫ f * g` equal to `∫ g`. -/
theorem integral_noiseTest_mul_of_eq_one {d : ℕ} (f g : NoiseTest d)
    (hone : ∀ y, g y ≠ 0 → f y = 1) :
  (∫ y : Vec d, f y * g y) = ∫ y : Vec d, g y := by
  apply integral_congr_ae
  filter_upwards with y
  by_cases hgy : g y = 0
  · simp [hgy]
  · simp [hone y hgy]

/-- Evaluations of white noise on a compact test and on its `L²`-orthogonal residual are
independent. -/
theorem indepFun_noise_projection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f g : NoiseTest d) (hf : f ≠ 0) :
    ProbabilityTheory.IndepFun (fun ω => W ω f)
      (fun ω => W ω (g - (((∫ z : Vec d, f z * g z) /
        (∫ z : Vec d, (f z)^2))) • f)) P := by
  have horth := integral_noiseTest_projection_orthogonal f g hf
  exact indepFun_noise_evaluations_of_orthogonal P W hmeas hwhite f _ horth

end EinsteinRelation.Sharpness
