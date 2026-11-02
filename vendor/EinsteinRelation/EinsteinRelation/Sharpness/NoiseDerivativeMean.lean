import EinsteinRelation.Sharpness.NoiseField
import EinsteinRelation.Sharpness.NoiseCentering
import EinsteinRelation.Sharpness.OuterCentering
import EinsteinRelation.Sharpness.IteratedConvolution
open MeasureTheory
namespace EinsteinRelation.Sharpness
private theorem derivativeMean_tanh_continuous : Continuous Real.tanh := by
  have heq : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')
private theorem derivativeMean_abs_tanh_le_one (t : ℝ) : |Real.tanh t| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos t),
    div_le_one (Real.cosh_pos t), abs_le]
  constructor
  · linarith [Real.cosh_add_sinh t, Real.exp_pos t]
  · linarith [Real.cosh_sub_sinh t, Real.exp_pos (-t)]
/-- Every actual iterated coordinate derivative of h is probability-integrable and centered.
Source main.tex1212–1218 and the derivative stationarity identities used in1261–1265.
The derivative moves onto the compact kernel; genuine product integrability and Fubini
justify the expectation. No differentiation under an unproved expectation is assumed. -/
theorem integrable_and_integral_iterated_smoothedNoiseField_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (ζ K : NoiseTest d) (is : List (Fin d)) (x : Vec d) :
    Integrable (fun ω => iteratedCoordinateDerivative is (smoothedNoiseField ζ K (W ω)) x) P ∧
      (∫ ω, iteratedCoordinateDerivative is (smoothedNoiseField ζ K (W ω)) x ∂P) = 0 := by
  have heq : (fun ω => iteratedCoordinateDerivative is (smoothedNoiseField ζ K (W ω)) x) =
      fun ω => ∫ y : Vec d, iteratedCoordinateDerivative is (ζ : Vec d → ℝ) y *
        Real.tanh (mollifiedNoise (W ω) K (x-y)) := by
    funext ω
    exact iteratedCoordinateDerivative_outer_convolution (ζ : Vec d → ℝ)
      (fun z => Real.tanh (mollifiedNoise (W ω) K z)) ζ.contDiff ζ.hasCompactSupport
      (derivativeMean_tanh_continuous.comp (continuous_mollifiedNoise (W ω) K)) is x
  rw [heq]
  exact integrable_and_integral_outer_field_eq_zero P
    (iteratedCoordinateDerivative is (ζ : Vec d → ℝ))
    (fun ω y => Real.tanh (mollifiedNoise (W ω) K y))
    (contDiff_iteratedCoordinateDerivative (ζ : Vec d → ℝ) ζ.contDiff is).continuous
    (hasCompactSupport_iteratedCoordinateDerivative (ζ : Vec d → ℝ) ζ.hasCompactSupport is)
    (derivativeMean_tanh_continuous.measurable.comp (measurable_mollifiedNoise_uncurry W hmeas K))
    (fun ω y => derivativeMean_abs_tanh_le_one _)
    (fun y => integral_tanh_mollifiedNoise_eq_zero P W hmeas hwhite K y) x
end EinsteinRelation.Sharpness
