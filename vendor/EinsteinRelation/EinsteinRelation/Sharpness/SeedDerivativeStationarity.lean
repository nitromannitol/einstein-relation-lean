import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Sharpness.CoordinateIterates
import EinsteinRelation.Sharpness.NoiseFieldDerivatives
import EinsteinRelation.Sharpness.NoiseFieldStationarity
import EinsteinRelation.Sharpness.NoiseMollifier
import EinsteinRelation.Sharpness.SeedField

/-! # Process-level stationarity of the actual canonical seed derivatives

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218, and the stationary
centering `E[∂₁ψ] = 0` in lines 1261–1265. The canonical seed is `seedField d W`, the literal field
`ζ * tanh(K * W)` with `ζ = K = mollifierNoiseTest d`.

For a fixed list of coordinates `is`, the literal iterated coordinate derivative of the seed at
each point equals the smoothed field of the derivative kernel `D_is ζ`, by the exact integral
derivative identity `iteratedCoordinateDerivative_smoothedNoiseField`. That derivative kernel is
itself an actual compact smooth test, so the process-level law
`identDistrib_smoothedNoiseField_process_translate` applies with the derivative as outer kernel and the same inner kernel `K`. No
stationarity of the derivative is assumed, and no expectation is differentiated under the integral.
The white-noise input is the frozen `External.IsWhiteNoiseLaw P` alone. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The iterated coordinate derivative `D_is ζ` of the canonical kernel `ζ = mollifierNoiseTest d`,
packaged as an actual compact smooth test. The `C^∞` and compact-support fields come from the
checked producers for iterated coordinate derivatives. No kernel is chosen: this is exactly the
derivative of `mollifierNoiseTest d` along `is`. -/
private noncomputable def canonicalDerivativeTest {d : ℕ} (is : List (Fin d)) : NoiseTest d where
  toFun := iteratedCoordinateDerivative is (mollifierNoiseTest d : Vec d → ℝ)
  contDiff' := contDiff_iteratedCoordinateDerivative (mollifierNoiseTest d : Vec d → ℝ)
    (mollifierNoiseTest d).contDiff is
  hasCompactSupport' :=
    hasCompactSupport_iteratedCoordinateDerivative (mollifierNoiseTest d : Vec d → ℝ)
      (mollifierNoiseTest d).hasCompactSupport is
  tsupport_subset' := Set.subset_univ _

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1218. The actual iterated
coordinate derivative of the canonical seed at a sample `W` and a point `x` is the literal smoothed
field of the derivative kernel `D_is ζ`, with the canonical inner kernel `K`. This is the exact
integral derivative identity, read as an equality of the two named fields. -/
private theorem iteratedCoordinateDerivative_seedField_eq_smoothed {d : ℕ} (is : List (Fin d))
    (W : NoiseSample d) (x : Vec d) :
    iteratedCoordinateDerivative is (seedField d W) x =
      smoothedNoiseField (canonicalDerivativeTest is) (mollifierNoiseTest d) W x :=
  iteratedCoordinateDerivative_smoothedNoiseField (mollifierNoiseTest d) (mollifierNoiseTest d)
    W is x

/-- Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218, with the stationary
centering in lines 1261–1265. For a white-noise law `P`, a list of coordinates `is`, an index type
`T`, a family `xs : T → Vec d`, and a shift `h`, the processes
`t ↦ ∂_is (ζ * tanh(K * W)) (h + xₜ)` and `t ↦ ∂_is (ζ * tanh(K * W)) xₜ` of actual canonical seed
derivatives are identically distributed under `P`, as `T → ℝ` with the evaluation product σ-algebra.
The shift law is applied to the derivative kernel `D_is ζ` and the canonical inner kernel `K`, and
the actual derivative arrays are then identified pointwise. -/
theorem identDistrib_seedField_derivative_process_translate {d : ℕ}
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P)
    (is : List (Fin d)) (T : Type) (xs : T → Vec d) (h : Vec d) :
    ProbabilityTheory.IdentDistrib
      (fun W : NoiseSample d => fun t : T =>
        iteratedCoordinateDerivative is (seedField d W) (h + xs t))
      (fun W : NoiseSample d => fun t : T =>
        iteratedCoordinateDerivative is (seedField d W) (xs t)) P P := by
  letI : IsProbabilityMeasure P := hP.1
  have hproc : ProbabilityTheory.IdentDistrib
      (fun W : NoiseSample d => fun t : T =>
        smoothedNoiseField (canonicalDerivativeTest is) (mollifierNoiseTest d) W (h + xs t))
      (fun W : NoiseSample d => fun t : T =>
        smoothedNoiseField (canonicalDerivativeTest is) (mollifierNoiseTest d) W (xs t)) P P :=
    identDistrib_smoothedNoiseField_process_translate P id
      (fun f => External.measurable_noiseEvaluation f) hP.2
      (canonicalDerivativeTest is) (mollifierNoiseTest d) T xs h
  have e1 : (fun W : NoiseSample d => fun t : T =>
        iteratedCoordinateDerivative is (seedField d W) (h + xs t)) =
      (fun W : NoiseSample d => fun t : T =>
        smoothedNoiseField (canonicalDerivativeTest is) (mollifierNoiseTest d) W (h + xs t)) := by
    funext W t
    exact iteratedCoordinateDerivative_seedField_eq_smoothed is W (h + xs t)
  have e2 : (fun W : NoiseSample d => fun t : T =>
        iteratedCoordinateDerivative is (seedField d W) (xs t)) =
      (fun W : NoiseSample d => fun t : T =>
        smoothedNoiseField (canonicalDerivativeTest is) (mollifierNoiseTest d) W (xs t)) := by
    funext W t
    exact iteratedCoordinateDerivative_seedField_eq_smoothed is W (xs t)
  rw [e1, e2]
  exact hproc

end EinsteinRelation.Sharpness
