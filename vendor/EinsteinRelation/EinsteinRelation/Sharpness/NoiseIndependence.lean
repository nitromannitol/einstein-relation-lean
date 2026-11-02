import EinsteinRelation.Sharpness.NoiseKernel
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Pair independence of noise evaluations on disjoint tests

Source: `paper/main.tex:1212–1216`, the internal finite-range construction
`h ≔ ζ * tanh(K * W)` in the proof of `sharp.example` (Proposition 7.1). The generic
white-noise law `hwhite` is an explicit hypothesis of `indepFun_noise_evaluations`. It
is sourced from the cited AKM Definition 5.1 / Proposition 5.14, and it is not a premise
of the final sharpness statement.

The theorem is a finite-range pair-independence leaf: for tests `f`, `g` with disjoint
supports, `W f` and `W g` are independent. It is not full field σ-algebra independence,
and it does not establish nondegeneracy of `h`. Independence is derived by factorizing the
joint dual characteristic function. The only probabilistic input is the Gaussian
characteristic formula `hwhite`, applied at the combined test `a • f + b • g`.
Linearity of `W` holds samplewise on the compact smooth test carrier of `NoiseKernel`.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Samplewise linearity of a distribution on the compact smooth test carrier. -/
theorem noise_eval_smul_add {d : ℕ} (W : NoiseSample d) (f g : NoiseTest d) (a b : ℝ) :
    W (a • f + b • g) = a * W f + b * W g := by
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Squares of compact smooth tests are integrable on coordinate space. -/
theorem noiseTest_sq_integrable {d : ℕ} (f : NoiseTest d) :
    Integrable (fun y : Vec d => (f y) ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (f.contDiff.continuous).pow 2
  · exact f.hasCompactSupport.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)

/-- Disjoint supports make the cross term of `∫ (a f + b g)²` vanish. -/
theorem noise_sq_integral_pair {d : ℕ} (f g : NoiseTest d) (hdisj : ∀ y, f y * g y = 0)
    (a b : ℝ) :
    (∫ y : Vec d, ((a • f + b • g) y) ^ 2) =
      a ^ 2 * (∫ y : Vec d, (f y) ^ 2) + b ^ 2 * (∫ y : Vec d, (g y) ^ 2) := by
  have hpt : ∀ y : Vec d, ((a • f + b • g) y) ^ 2 = a ^ 2 * (f y) ^ 2 + b ^ 2 * (g y) ^ 2 := by
    intro y
    change (a * f y + b * g y) ^ 2 = a ^ 2 * (f y) ^ 2 + b ^ 2 * (g y) ^ 2
    linear_combination (2 * a * b) * hdisj y
  simp_rw [hpt]
  rw [integral_add ((noiseTest_sq_integrable f).const_mul (a ^ 2))
      ((noiseTest_sq_integrable g).const_mul (b ^ 2)),
    integral_const_mul, integral_const_mul]

/-- The dual characteristic function of the image of `P` under `X` is the expectation of
`exp (L (X ω) * I)` over `P`. -/
private theorem charFunDual_map_eq_integral_exp {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) {X : Ω → E} (hX : Measurable X)
    (L : StrongDual ℝ E) :
    charFunDual (P.map X) L = ∫ ω, Complex.exp (((L (X ω) : ℝ) : ℂ) * Complex.I) ∂P := by
  have hc : Continuous fun v : E => Complex.exp (((L v : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  rw [charFunDual_apply, integral_map hX.aemeasurable hc.aestronglyMeasurable]

/-- Finite-range pair independence of noise evaluations on disjoint tests.

Conditional on the generic Gaussian characteristic law `hwhite`, the evaluations `W f`
and `W g` are independent whenever `f * g = 0` pointwise. This is a finite-range leaf
from `paper/main.tex:1212–1216`, not full field independence or nondegeneracy of `h`. -/
theorem indepFun_noise_evaluations {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f g : NoiseTest d) (hdisj : ∀ y, f y * g y = 0) :
    ProbabilityTheory.IndepFun (fun ω => W ω f) (fun ω => W ω g) P := by
  refine (ProbabilityTheory.indepFun_iff_charFunDual_prod (hmeas f).aemeasurable
    (hmeas g).aemeasurable).2 ?_
  intro L
  have hX : Measurable (fun ω => W ω f) := hmeas f
  have hY : Measurable (fun ω => W ω g) := hmeas g
  have hXY : Measurable (fun ω => (W ω f, W ω g)) := hX.prodMk hY
  show charFunDual (P.map fun ω => (W ω f, W ω g)) L =
    charFunDual (P.map fun ω => W ω f) (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) *
      charFunDual (P.map fun ω => W ω g) (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ))
  rw [charFunDual_map_eq_integral_exp P hXY L,
    charFunDual_map_eq_integral_exp P hX (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)),
    charFunDual_map_eq_integral_exp P hY (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ))]
  -- Coordinates of the continuous linear functional on `ℝ × ℝ`.
  have hLpair : ∀ x y : ℝ, L (x, y) = x * L (1, 0) + y * L (0, 1) := by
    intro x y
    have hxy : ((x, y) : ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hxy, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hInl : ∀ x : ℝ, (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) x = x * L (1, 0) := by
    intro x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hLpair x 0]
    ring
  have hInr : ∀ y : ℝ, (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) y = y * L (0, 1) := by
    intro y
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hLpair 0 y]
    ring
  -- The joint factor equals the Gaussian factor at the combined test `L(1,0) • f + L(0,1) • g`.
  have hLHS : (∫ ω, Complex.exp (((L (W ω f, W ω g) : ℝ) : ℂ) * Complex.I) ∂P) =
      ∫ ω, Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
        (W ω (L (1, 0) • f + L (0, 1) • g) : ℂ)) ∂P := by
    congr 1
    funext ω
    congr 1
    rw [hLpair (W ω f) (W ω g), noise_eval_smul_add (W ω) f g (L (1, 0)) (L (0, 1))]
    push_cast
    ring
  have hR1 : (∫ ω, Complex.exp ((((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) (W ω f) : ℝ) : ℂ) *
      Complex.I) ∂P) =
      ∫ ω, Complex.exp (Complex.I * ((L (1, 0) : ℝ) : ℂ) * (W ω f : ℂ)) ∂P := by
    congr 1
    funext ω
    congr 1
    rw [hInl (W ω f)]
    push_cast
    ring
  have hR2 : (∫ ω, Complex.exp ((((L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) (W ω g) : ℝ) : ℂ) *
      Complex.I) ∂P) =
      ∫ ω, Complex.exp (Complex.I * ((L (0, 1) : ℝ) : ℂ) * (W ω g : ℂ)) ∂P := by
    congr 1
    funext ω
    congr 1
    rw [hInr (W ω g)]
    push_cast
    ring
  have hH := hwhite (L (1, 0) • f + L (0, 1) • g) 1
  have hF := hwhite f (L (1, 0))
  have hG := hwhite g (L (0, 1))
  rw [hLHS, hH, noise_sq_integral_pair f g hdisj (L (1, 0)) (L (0, 1)), hR1, hR2, hF, hG]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end EinsteinRelation.Sharpness
