import EinsteinRelation.Sharpness.NoiseKernel
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Centering of the actual bounded tanh-noise field

`paper/main.tex:1212–1216`: the bounded field `tanh(K * W)` before outer convolution is
centered. For a compact smooth test `K` and a point `x`, the sample `Y = W(K(x - ·))` of
unit white noise has characteristic function `exp(-r² ‖K‖²/2)`, which is even in `r`
(`mollifiedNoise_characteristic`). Uniqueness of characteristic functions gives
`P.map (-Y) = P.map Y`; since `tanh` is odd, `E tanh Y` equals its own negative, hence
vanishes. Only the all-test Gaussian primitive `hwhite` is used. No integrability,
boundedness, symmetry, or range assumption is added.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The real hyperbolic tangent is continuous, as the quotient of `sinh` and `cosh`. -/
private theorem continuous_tanh_real : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
    funext x
    rw [Real.tanh_eq_sinh_div_cosh]
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

/-- A real random variable whose characteristic function is even in the frequency has the
same law as its negative. Uniqueness of characteristic functions gives the identity. -/
private theorem map_neg_eq_map_of_even_charFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (heven : ∀ t : ℝ, (∫ ω, Complex.exp ((t : ℂ) * (Y ω : ℂ) * Complex.I) ∂P) =
      ∫ ω, Complex.exp (((-t : ℝ) : ℂ) * (Y ω : ℂ) * Complex.I) ∂P) :
    P.map (fun ω => -Y ω) = P.map Y := by
  apply Measure.ext_of_charFun
  funext t
  have hcont : Continuous fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
    fun_prop
  have h1 : (∫ x, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂(P.map (fun ω => -Y ω))) =
      ∫ ω, Complex.exp ((t : ℂ) * ((-Y ω : ℝ) : ℂ) * Complex.I) ∂P :=
    integral_map hY.neg.aemeasurable hcont.aestronglyMeasurable
  have h2 : (∫ ω, Complex.exp ((t : ℂ) * ((-Y ω : ℝ) : ℂ) * Complex.I) ∂P) =
      ∫ ω, Complex.exp (((-t : ℝ) : ℂ) * (Y ω : ℂ) * Complex.I) ∂P := by
    congr 1
    funext ω
    congr 1
    simp only [Complex.ofReal_neg]
    ring
  have h3 : (∫ x, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂(P.map Y)) =
      ∫ ω, Complex.exp ((t : ℂ) * (Y ω : ℂ) * Complex.I) ∂P :=
    integral_map hY.aemeasurable hcont.aestronglyMeasurable
  have hL := charFun_apply_real (μ := P.map (fun ω => -Y ω)) t
  have hR := charFun_apply_real (μ := P.map Y) t
  exact hL.trans (h1.trans (h2.trans ((heven t).symm.trans (h3.symm.trans hR.symm))))

/-- The first convolution of the actual unit white noise with a compact test is centered:
the expectation of `tanh` of its sample vanishes. The argument is the Gaussian reflection
law above together with the oddness of `tanh`; it uses the all-test Gaussian primitive. -/
theorem integral_tanh_mollifiedNoise_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (K : NoiseTest d) (x : Vec d) :
    (∫ ω, Real.tanh (mollifiedNoise (W ω) K x) ∂P) = 0 := by
  have hY : Measurable (fun ω => mollifiedNoise (W ω) K x) :=
    measurable_mollifiedNoise W hmeas K x
  have hreorder : ∀ r : ℝ,
      (∫ ω, Complex.exp ((r : ℂ) * (mollifiedNoise (W ω) K x : ℂ) * Complex.I) ∂P) =
        ∫ ω, Complex.exp (Complex.I * (r : ℂ) * (mollifiedNoise (W ω) K x : ℂ)) ∂P := by
    intro r
    congr 1
    funext ω
    congr 1
    ring
  have heven : ∀ t : ℝ,
      (∫ ω, Complex.exp ((t : ℂ) * (mollifiedNoise (W ω) K x : ℂ) * Complex.I) ∂P) =
        ∫ ω, Complex.exp (((-t : ℝ) : ℂ) * (mollifiedNoise (W ω) K x : ℂ) * Complex.I) ∂P := by
    intro t
    rw [hreorder t, hreorder (-t), mollifiedNoise_characteristic P W hwhite K x t,
      mollifiedNoise_characteristic P W hwhite K x (-t), Complex.ofReal_neg, neg_sq]
  have hmap : P.map (fun ω => -mollifiedNoise (W ω) K x) =
      P.map (fun ω => mollifiedNoise (W ω) K x) :=
    map_neg_eq_map_of_even_charFun P (fun ω => mollifiedNoise (W ω) K x) hY heven
  have hT : Continuous Real.tanh := continuous_tanh_real
  have hA : (∫ ω, Real.tanh (-mollifiedNoise (W ω) K x) ∂P) =
      ∫ y, Real.tanh y ∂(P.map (fun ω => -mollifiedNoise (W ω) K x)) :=
    (integral_map hY.neg.aemeasurable hT.aestronglyMeasurable).symm
  have hB : (∫ ω, Real.tanh (mollifiedNoise (W ω) K x) ∂P) =
      ∫ y, Real.tanh y ∂(P.map (fun ω => mollifiedNoise (W ω) K x)) :=
    (integral_map hY.aemeasurable hT.aestronglyMeasurable).symm
  have hodd : (∫ ω, Real.tanh (-mollifiedNoise (W ω) K x) ∂P) =
      -(∫ ω, Real.tanh (mollifiedNoise (W ω) K x) ∂P) := by
    simp only [Real.tanh_neg, integral_neg]
  rw [hmap] at hA
  linarith

end EinsteinRelation.Sharpness
