import EinsteinRelation.Sharpness.NoiseContinuity
import EinsteinRelation.Sharpness.OuterConvolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Arithmetic

/-! # The literal smoothed distribution field

Source paper/main.tex1212–1216: h = ζ * tanh(K * W), on actual LF distributions.
The two kernels are given genuine compact smooth tests; the canonical normalized
ζ remains GENERAL-owned. These definitions and consumers do not assert Gaussian
existence, stationarity, finite range or h nondegeneracy.
-/
open MeasureTheory
namespace EinsteinRelation.Sharpness

/-- The literal two-stage field ζ * tanh(K * W) at an actual distribution sample. -/
noncomputable def smoothedNoiseField {d : ℕ} (ζ K : NoiseTest d) (W : NoiseSample d)
    (x : Vec d) : ℝ :=
  ∫ y : Vec d, ζ y * Real.tanh (mollifiedNoise W K (x-y))

@[simp] theorem smoothedNoiseField_apply {d : ℕ} (ζ K : NoiseTest d) (W : NoiseSample d)
    (x : Vec d) :
    smoothedNoiseField ζ K W x = ∫ y : Vec d, ζ y * Real.tanh (mollifiedNoise W K (x-y)) := rfl

private theorem continuous_noiseField_tanh : Continuous Real.tanh := by
  have heq : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')

/-- The literal convolution integrand is integrable for every sample and point. -/
theorem integrable_smoothedNoiseField_integrand {d : ℕ} (ζ K : NoiseTest d)
    (W : NoiseSample d) (x : Vec d) :
    Integrable (fun y : Vec d => ζ y * Real.tanh (mollifiedNoise W K (x-y))) := by
  have hc : Continuous (fun y : Vec d => ζ y * Real.tanh (mollifiedNoise W K (x-y))) :=
    ζ.contDiff.continuous.mul (continuous_noiseField_tanh.comp
      ((continuous_mollifiedNoise W K).comp (continuous_const.sub continuous_id)))
  have hs : HasCompactSupport
      (fun y : Vec d => ζ y * Real.tanh (mollifiedNoise W K (x-y))) :=
    ζ.hasCompactSupport.mul_right
  exact hc.integrable_of_hasCompactSupport hs

/-- Every actual sample is C∞ after the outer convolution. -/
theorem contDiff_smoothedNoiseField {d : ℕ} (ζ K : NoiseTest d) (W : NoiseSample d) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothedNoiseField ζ K W) :=
  contDiff_outer_convolution_tanh (ζ : Vec d → ℝ) (mollifiedNoise W K)
    ζ.contDiff ζ.hasCompactSupport (continuous_mollifiedNoise W K)

/-- Deterministic amplitude control by the fixed outer kernel's actual L1 mass. -/
theorem abs_smoothedNoiseField_le {d : ℕ} (ζ K : NoiseTest d) (W : NoiseSample d)
    (x : Vec d) : |smoothedNoiseField ζ K W x| ≤ ∫ y : Vec d, |ζ y| :=
  abs_outer_convolution_tanh_le (ζ : Vec d → ℝ) (mollifiedNoise W K)
    ζ.contDiff.continuous ζ.hasCompactSupport (continuous_mollifiedNoise W K) x

/-- Measurability of the actual field jointly in sample and spatial point follows from
measurable noise evaluations and the actual Lebesgue integral, without a strong-dual Borel claim. -/
theorem measurable_smoothedNoiseField_uncurry {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f)) (ζ K : NoiseTest d) :
    Measurable (fun p : Ω × Vec d => smoothedNoiseField ζ K (W p.1) p.2) := by
  have hG := measurable_mollifiedNoise_uncurry W hmeas K
  have hshift : Measurable (fun p : (Ω × Vec d) × Vec d => (p.1.1, p.1.2-p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd)
  have hT : Measurable (fun p : (Ω × Vec d) × Vec d =>
      Real.tanh (mollifiedNoise (W p.1.1) K (p.1.2-p.2))) :=
    continuous_noiseField_tanh.measurable.comp (hG.comp hshift)
  have hζ : Measurable (fun p : (Ω × Vec d) × Vec d => ζ p.2) :=
    ζ.contDiff.continuous.measurable.comp measurable_snd
  have hsm : StronglyMeasurable (fun p : (Ω × Vec d) × Vec d =>
      ζ p.2 * Real.tanh (mollifiedNoise (W p.1.1) K (p.1.2-p.2))) :=
    (hζ.mul hT).stronglyMeasurable
  exact hsm.integral_prod_right'.measurable
end EinsteinRelation.Sharpness