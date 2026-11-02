import EinsteinRelation.Sharpness.NoiseKernel
import EinsteinRelation.Sharpness.NoiseVariance
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian marginals of actual compact-test noise evaluations

AKM Definition 5.1 and Proposition 5.14, used at `paper/main.tex:1212–1216`.
Under the common Gaussian characteristic-function prefix, each actual evaluation
`ω ↦ W ω f` of a compact smooth test is a centred Gaussian whose variance is the
fixed L² mass of `f`. A nonzero test therefore has strictly positive upper-tail
probability.

This is raw-test nondegeneracy only. It does not give nondegeneracy of the
outer-convolved `h`, nor full σ-independence of the noise family. No Gaussian
tail inequality and no nonconstancy of the field is assumed.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The characteristic function of one actual test evaluation, obtained by pushing
the Fourier identity through the measurable evaluation map. -/
private theorem charFun_map_noise_evaluation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f : NoiseTest d) (t : ℝ) :
    charFun (P.map (fun ω => W ω f)) t =
      Complex.exp (((-(1/2 : ℝ))*t^2*∫ y : Vec d, (f y)^2) : ℂ) := by
  have hc : Continuous (fun x : ℝ => Complex.exp (t * x * Complex.I)) := by
    fun_prop
  have hint : charFun (P.map (fun ω => W ω f)) t =
      ∫ ω, Complex.exp (Complex.I * (t : ℂ) * (W ω f : ℂ)) ∂P := by
    rw [charFun_apply_real, integral_map (hmeas f).aemeasurable hc.aestronglyMeasurable]
    congr 1
    funext ω
    congr 1
    ring
  rw [hint]
  exact hwhite f t

/-- The actual evaluation law of a compact smooth test is the centred Gaussian with
variance `∫ f²`, identified through characteristic functions. -/
theorem map_noise_evaluation_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f : NoiseTest d) :
    P.map (fun ω => W ω f) = ProbabilityTheory.gaussianReal 0
      ⟨(∫ y : Vec d, (f y)^2), integral_nonneg (fun y => sq_nonneg (f y))⟩ := by
  haveI : IsProbabilityMeasure (P.map (fun ω => W ω f)) :=
    inferInstance
  haveI : IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0
      ⟨(∫ y : Vec d, (f y)^2), integral_nonneg (fun y => sq_nonneg (f y))⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_map_noise_evaluation P W hmeas hwhite f t]
  refine Eq.trans ?_ (ProbabilityTheory.charFun_gaussianReal (μ := 0)
    (v := ⟨(∫ y : Vec d, (f y)^2), integral_nonneg (fun y => sq_nonneg (f y))⟩) t).symm
  congr 1
  have hv : (((⟨(∫ y : Vec d, (f y)^2), integral_nonneg (fun y => sq_nonneg (f y))⟩ :
      NNReal) : ℝ)) = ∫ y : Vec d, (f y)^2 := rfl
  push_cast [NNReal.coe_mk, hv]
  first
    | (exact rfl; done)
    | (ring_nf; (congr 3 <;> first | exact hv.symm | rfl); done)
    | (ring_nf; (congr 2 <;> first | exact congrArg _ hv.symm | rfl); done)
    | (ring_nf; simp only [hv]; done)
    | (ring_nf; norm_num [NNReal.coe_mk]; done)

/-- Every nonzero actual compact test has strictly positive upper-tail probability,
because its Gaussian evaluation law charges every nonempty open half-line. -/
theorem noise_evaluation_upper_tail_pos {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f : NoiseTest d) (hf : f ≠ 0) (a : ℝ) :
    0 < P {ω | a < W ω f} := by
  have hv : (⟨(∫ y : Vec d, (f y)^2), integral_nonneg (fun y => sq_nonneg (f y))⟩ :
      NNReal) ≠ 0 := by
    intro h
    have h' := congrArg NNReal.toReal h
    exact (noiseTest_l2_mass_pos f hf).ne' h'
  have hG : P.map (fun ω => W ω f) (Set.Ioi a) ≠ 0 := by
    rw [map_noise_evaluation_eq_gaussianReal P W hmeas hwhite f]
    intro h0
    have h1 : volume (Set.Ioi a) = 0 :=
      ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 hv h0
    rw [Real.volume_Ioi] at h1
    exact ENNReal.top_ne_zero h1
  have hmap : P.map (fun ω => W ω f) (Set.Ioi a) = P {ω | a < W ω f} :=
    Measure.map_apply (hmeas f) measurableSet_Ioi
  rw [← hmap]
  exact pos_iff_ne_zero.mpr hG

end EinsteinRelation.Sharpness
