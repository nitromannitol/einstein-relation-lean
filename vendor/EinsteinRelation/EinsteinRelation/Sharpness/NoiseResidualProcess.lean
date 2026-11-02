import EinsteinRelation.Sharpness.NoiseProcessIndependence
import EinsteinRelation.Sharpness.NoiseProjection
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Independence.Basic

/-! # Scalar independence from the orthogonal residual process

Source: `paper/main.tex:1212–1216`, the internal finite-range construction `h ≔ ζ * tanh(K * W)`
in the proof of `sharp.example` (Proposition 7.1). The generic Gaussian characteristic law
`hwhite` is an explicit hypothesis here, as in `NoiseProcessIndependence` and `NoiseProjection`.
It is not a premise of the final sharpness statement.

For a nonzero actual compact smooth test `f` and an arbitrary family `G : T → NoiseTest d`, the
scalar evaluation `W f` is independent of the whole process `t ↦ W (G t - c t • f)`, where
`c t = (∫ f * G t) / (∫ f²)` is the `L²`-projection coefficient. Each residual test is
`L²`-orthogonal to `f`, so the statement is the joint finite-block factorization of
`indepFun_noise_processes_of_orthogonal` applied to the one-element constant family
`fun _ : Unit => f`, followed by evaluation at the unique coordinate.

Both output processes carry the ordinary `Pi` evaluation σ-algebra. The proof uses no
nondegeneracy of `h`, no pairwise-only independence, and no residual-independence premise.
Producing the residual tests from the kernel translates, and the covariance constancy on the
cutoff support, are separate obligations.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Independence of the scalar evaluation `W f` from the process of its `L²`-orthogonal residuals
`t ↦ W (G t - c t • f)`, for a nonzero compact smooth test `f`. Both sides carry the ordinary
`Pi` evaluation σ-algebra. -/
theorem indepFun_noise_residual_process {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f : NoiseTest d) (hf : f ≠ 0) (T : Type*) (G : T → NoiseTest d) :
    ProbabilityTheory.IndepFun (fun ω => W ω f)
      (fun ω => fun t : T => W ω (G t - (((∫ y : Vec d, f y * G t y) /
        (∫ y : Vec d, (f y)^2))) • f)) P := by
  -- The constant one-element family against the residual family is orthogonal.
  have hproc : ProbabilityTheory.IndepFun (fun ω => fun _ : Unit => W ω f)
      (fun ω => fun t : T => W ω (G t - (((∫ y : Vec d, f y * G t y) /
        (∫ y : Vec d, (f y)^2))) • f)) P :=
    indepFun_noise_processes_of_orthogonal P W hmeas hwhite Unit T (fun _ => f)
      (fun t => G t - (((∫ y : Vec d, f y * G t y) / (∫ y : Vec d, (f y)^2))) • f)
      (fun _ t => integral_noiseTest_projection_orthogonal f (G t) hf)
  -- Evaluation at the unique coordinate recovers `W f`; the residual process is the identity.
  have hcoord : Measurable (fun v : Unit → ℝ => v Unit.unit) :=
    measurable_pi_apply Unit.unit
  have hid : Measurable (id : (T → ℝ) → (T → ℝ)) := measurable_id
  exact ProbabilityTheory.IndepFun.comp hproc hcoord hid

end EinsteinRelation.Sharpness
