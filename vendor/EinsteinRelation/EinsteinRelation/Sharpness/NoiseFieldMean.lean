import EinsteinRelation.Sharpness.NoiseField
import EinsteinRelation.Sharpness.NoiseCentering
import EinsteinRelation.Sharpness.OuterCentering
open MeasureTheory
namespace EinsteinRelation.Sharpness
private theorem noiseMean_tanh_continuous : Continuous Real.tanh := by
  have heq : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')
private theorem noiseMean_abs_tanh_le_one (t : ℝ) : |Real.tanh t| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos t)]
  apply (div_le_one (Real.cosh_pos t)).mpr
  have hsq := Real.cosh_sq_sub_sinh_sq t
  have hc := Real.cosh_pos t
  have ha := sq_abs (Real.sinh t)
  nlinarith [sq_nonneg (Real.sinh t)]
/-- The actual smoothed white-noise field is integrable on its probability space and centered.
Source main.tex1212–1216; joint measurability, boundedness and product integrability are proved. -/
theorem integrable_and_integral_smoothedNoiseField_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (ζ K : NoiseTest d) (x : Vec d) :
    Integrable (fun ω => smoothedNoiseField ζ K (W ω) x) P ∧
      (∫ ω, smoothedNoiseField ζ K (W ω) x ∂P) = 0 := by
  exact integrable_and_integral_outer_field_eq_zero P (ζ : Vec d → ℝ)
    (fun ω y => Real.tanh (mollifiedNoise (W ω) K y)) ζ.contDiff.continuous ζ.hasCompactSupport
    (noiseMean_tanh_continuous.measurable.comp (measurable_mollifiedNoise_uncurry W hmeas K))
    (fun ω y => noiseMean_abs_tanh_le_one _) 
    (fun y => integral_tanh_mollifiedNoise_eq_zero P W hmeas hwhite K y) x
end EinsteinRelation.Sharpness
