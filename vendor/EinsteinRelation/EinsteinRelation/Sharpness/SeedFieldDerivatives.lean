import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Sharpness.NoiseContinuity
import EinsteinRelation.Sharpness.NoiseDerivativeMean
import EinsteinRelation.Sharpness.NoiseFieldDerivatives
import EinsteinRelation.Sharpness.NoiseGradientScale
import EinsteinRelation.Sharpness.SeedField
import Mathlib.MeasureTheory.Integral.Prod

/-! # Derivatives of the canonical sharpness seed

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218. The seed
`h ≔ ζ * tanh(K * W)` is `seedField d W` with `K = ζ = mollifierNoiseTest d`. Line 1218 chooses
`ε > 0` so that `ε h` has Euclidean gradient at most `1/4`. Lines 1261–1265 use the stationary
centering of the derivatives of `h`.

Each public statement below is the literal canonical specialization of a checked generic result.
The scale and all derivative constants are chosen before the sample `W` and the point `x`. The only
probabilistic input is the frozen white-noise law `External.IsWhiteNoiseLaw P`. No extra
hypothesis, and no differentiation under the expectation, is used.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- `Real.tanh` is continuous, as the quotient of the continuous `sinh` by the everywhere positive
`cosh`. The pinned Mathlib has no `Real.continuous_tanh`, so the fact is derived here. -/
private theorem seedDerivative_continuous_tanh : Continuous Real.tanh := by
  have heq : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218. For the canonical kernels
there is one scale `ε > 0`, chosen before the sample `W` and the point `x`, such that the Euclidean
gradient of `ε * seedField d W` is at most `1/4` everywhere. -/
theorem exists_seedField_gradient_scale (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ) := by
  obtain ⟨ε, hε, h⟩ := exists_uniform_smoothedNoiseField_gradient_scale (mollifierNoiseTest d)
  exact ⟨ε, hε, fun W x => h (mollifierNoiseTest d) W x⟩

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218. For every list of
coordinates, the iterated coordinate derivatives of the canonical seed are bounded by one
deterministic constant, uniformly in the actual sample `W` and the point `x`. -/
theorem exists_uniform_seedField_derivative_bound (d : ℕ) (is : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : NoiseSample d) (x : Vec d),
      |iteratedCoordinateDerivative is (seedField d W) x| ≤ C := by
  obtain ⟨C, hC, h⟩ :=
    exists_uniform_smoothedNoiseField_derivative_bound (mollifierNoiseTest d) is
  exact ⟨C, hC, fun W x => h (mollifierNoiseTest d) W x⟩

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218, and the centering of the
derivatives in lines 1261–1265. For a white-noise law `P` and every list of coordinates, the
iterated coordinate derivative of the canonical seed at each point is `P`-integrable with mean
zero. The derivative falls on the fixed kernel, and genuine Fubini justifies the expectation. -/
theorem integrable_and_integral_seedField_derivative_eq_zero (d : ℕ)
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P)
    (is : List (Fin d)) (x : Vec d) :
    Integrable (fun W : NoiseSample d => iteratedCoordinateDerivative is (seedField d W) x) P ∧
      (∫ W : NoiseSample d, iteratedCoordinateDerivative is (seedField d W) x ∂P) = 0 := by
  letI : IsProbabilityMeasure P := hP.1
  exact integrable_and_integral_iterated_smoothedNoiseField_eq_zero P id
    (fun f => External.measurable_noiseEvaluation f) hP.2
    (mollifierNoiseTest d) (mollifierNoiseTest d) is x

/-- Joint measurability of the iterated coordinate derivative of the canonical seed in the actual
sample and the point. This is the Fubini producer `StronglyMeasurable.integral_prod_right'`
applied to the outer convolution, exactly as for `measurable_smoothedNoiseField_uncurry`. -/
theorem measurable_seedField_iteratedCoordinateDerivative_uncurry (d : ℕ) (is : List (Fin d)) :
    Measurable (fun p : NoiseSample d × Vec d =>
      iteratedCoordinateDerivative is (seedField d p.1) p.2) := by
  have hG : Measurable (fun p : NoiseSample d × Vec d =>
      mollifiedNoise (id p.1) (mollifierNoiseTest d) p.2) :=
    measurable_mollifiedNoise_uncurry (id : NoiseSample d → NoiseSample d)
      (fun f => External.measurable_noiseEvaluation f) (mollifierNoiseTest d)
  have hshift : Measurable (fun q : (NoiseSample d × Vec d) × Vec d =>
      (q.1.1, q.1.2 - q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd)
  have hT : Measurable (fun q : (NoiseSample d × Vec d) × Vec d =>
      Real.tanh (mollifiedNoise q.1.1 (mollifierNoiseTest d) (q.1.2 - q.2))) :=
    seedDerivative_continuous_tanh.measurable.comp (hG.comp hshift)
  have hD : Continuous (iteratedCoordinateDerivative is (mollifierNoiseTest d : Vec d → ℝ)) :=
    (contDiff_iteratedCoordinateDerivative (mollifierNoiseTest d : Vec d → ℝ)
      (mollifierNoiseTest d).contDiff is).continuous
  have hDm : Measurable (fun q : (NoiseSample d × Vec d) × Vec d =>
      iteratedCoordinateDerivative is (mollifierNoiseTest d : Vec d → ℝ) q.2) :=
    hD.measurable.comp measurable_snd
  have hsm : StronglyMeasurable (fun q : (NoiseSample d × Vec d) × Vec d =>
      iteratedCoordinateDerivative is (mollifierNoiseTest d : Vec d → ℝ) q.2 *
        Real.tanh (mollifiedNoise q.1.1 (mollifierNoiseTest d) (q.1.2 - q.2))) :=
    (hDm.mul hT).stronglyMeasurable
  have heq : (fun p : NoiseSample d × Vec d =>
      iteratedCoordinateDerivative is (seedField d p.1) p.2) =
      fun p : NoiseSample d × Vec d => ∫ y : Vec d,
        iteratedCoordinateDerivative is (mollifierNoiseTest d : Vec d → ℝ) y *
          Real.tanh (mollifiedNoise p.1 (mollifierNoiseTest d) (p.2 - y)) := by
    funext p
    exact iteratedCoordinateDerivative_smoothedNoiseField (mollifierNoiseTest d)
      (mollifierNoiseTest d) p.1 is p.2
  rw [heq]
  exact hsm.integral_prod_right'.measurable

/-- Measurability of the iterated coordinate derivative of the canonical seed at a fixed point, as a
function of the actual sample. -/
theorem measurable_seedField_iteratedCoordinateDerivative (d : ℕ) (is : List (Fin d))
    (x : Vec d) :
    Measurable (fun W : NoiseSample d => iteratedCoordinateDerivative is (seedField d W) x) := by
  have hpair : Measurable (fun W : NoiseSample d => (W, x)) :=
    measurable_id.prodMk measurable_const
  exact Measurable.comp (g := fun p : NoiseSample d × Vec d =>
      iteratedCoordinateDerivative is (seedField d p.1) p.2)
    (f := fun W : NoiseSample d => (W, x))
    (measurable_seedField_iteratedCoordinateDerivative_uncurry d is) hpair

end EinsteinRelation.Sharpness
