import EinsteinRelation.Sharpness.NoiseCompactCovariance
import EinsteinRelation.Sharpness.NoiseResidualProcess
import EinsteinRelation.Sharpness.NoiseVariance
import EinsteinRelation.Sharpness.SeedField
import Mathlib.Probability.Independence.Basic

/-! # Scalar residual split of the canonical seed field

Source `paper/main.tex:1212–1216`, the internal construction `h ≔ ζ * tanh(K * W)` in
`sharp.example` (Proposition 7.1). The canonical kernel is `mollifierNoiseTest d` for both `ζ`
and `K`, exactly as in `seedField`, so the first convolution is `mollifiedNoise W K (0 - y)`.

The auxiliary nonzero compact test `f` is chosen before any white-noise law. By
`exists_noiseTest_constant_compact_covariance` its integral against every reflected kernel
`u ↦ K (0 - y - u)`, with `y ∈ tsupport ζ`, equals `∫ K = 1`. The `L²` projection coefficient is
therefore `(∫ f²)⁻¹`, and the residual evaluation at `y` is
`mollifiedNoise W K (0 - y) - (∫ f²)⁻¹ * W f`. Independence of `W f` from these residuals is
`indepFun_noise_residual_process`, transported along this pointwise identity. Positivity of
`(∫ f²)⁻¹` is `noiseTest_l2_mass_pos`.

This file proves only the scalar split. It does not prove nondegeneracy of the outer-convolved
field, the compact residual bound, or the Gaussian tail estimates.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Samplewise linearity of a distribution on a test minus a scalar multiple of another test. -/
private theorem noise_eval_sub_smul {d : ℕ} (W : NoiseSample d) (g f : NoiseTest d) (c : ℝ) :
    W (g - c • f) = W g - c * W f := by
  rw [map_sub, map_smul, smul_eq_mul]

/-- The canonical seed kernel admits one nonzero auxiliary test `f`, fixed before the noise law,
whose scalar residual split against the first convolution is independent of `W f`. -/
theorem exists_seedField_scalar_residual_split (d : ℕ) :
    ∃ f : NoiseTest d, f ≠ 0 ∧
      0 < (∫ u : Vec d, (f u)^2)⁻¹ ∧
      ∀ P : Measure (NoiseSample d), External.IsWhiteNoiseLaw P →
        ProbabilityTheory.IndepFun (fun W : NoiseSample d => W f)
          (fun W : NoiseSample d => fun y : tsupport (mollifierNoiseTest d : Vec d → ℝ) =>
            mollifiedNoise W (mollifierNoiseTest d) (0-y.1) -
              (∫ u : Vec d, (f u)^2)⁻¹ * W f) P := by
  -- The test is chosen first: its covariance with every reflected kernel is `∫ K = 1`.
  obtain ⟨f, hf, hcov⟩ := exists_noiseTest_constant_compact_covariance
    (mollifierNoiseTest d) (mollifierNoiseTest d) (0 : Vec d)
  have hK : (∫ u : Vec d, mollifierNoiseTest d u) = 1 := by
    simp only [mollifierNoiseTest_apply]
    exact integral_mollifier d
  refine ⟨f, hf, inv_pos.mpr (noiseTest_l2_mass_pos f hf), ?_⟩
  intro P hP
  letI : IsProbabilityMeasure P := hP.1
  have hone : ∀ y : tsupport (mollifierNoiseTest d : Vec d → ℝ),
      (∫ u : Vec d, f u * kernelTest (mollifierNoiseTest d) (0 - y.1) u) = 1 :=
    fun y => (hcov y.1 y.2).trans hK
  have hpt : ∀ (ω : NoiseSample d) (y : tsupport (mollifierNoiseTest d : Vec d → ℝ)),
      ω (kernelTest (mollifierNoiseTest d) (0 - y.1) -
          ((∫ u : Vec d, f u * kernelTest (mollifierNoiseTest d) (0 - y.1) u) /
            (∫ u : Vec d, (f u)^2)) • f) =
        mollifiedNoise ω (mollifierNoiseTest d) (0 - y.1) -
          (∫ u : Vec d, (f u)^2)⁻¹ * ω f := by
    intro ω y
    rw [hone y, one_div]
    exact noise_eval_sub_smul ω (kernelTest (mollifierNoiseTest d) (0 - y.1)) f
      ((∫ u : Vec d, (f u)^2)⁻¹)
  have hproc := indepFun_noise_residual_process P (id : NoiseSample d → NoiseSample d)
    (fun g => External.measurable_noiseEvaluation g) hP.2 f hf _
    (fun y : tsupport (mollifierNoiseTest d : Vec d → ℝ) =>
      kernelTest (mollifierNoiseTest d) (0 - y.1))
  have hfun : (fun W : NoiseSample d => fun y : tsupport (mollifierNoiseTest d : Vec d → ℝ) =>
        mollifiedNoise W (mollifierNoiseTest d) (0-y.1) -
          (∫ u : Vec d, (f u)^2)⁻¹ * W f) =
      (fun ω : NoiseSample d => fun y : tsupport (mollifierNoiseTest d : Vec d → ℝ) =>
        ω (kernelTest (mollifierNoiseTest d) (0 - y.1) -
          ((∫ u : Vec d, f u * kernelTest (mollifierNoiseTest d) (0 - y.1) u) /
            (∫ u : Vec d, (f u)^2)) • f)) := by
    funext ω y
    exact (hpt ω y).symm
  rw [hfun]
  exact hproc

end EinsteinRelation.Sharpness
