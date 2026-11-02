import EinsteinRelation.Sharpness.NoiseKernel
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Probability.IdentDistrib
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp

/-! # Stationarity of the raw finite-dimensional laws of the first convolution `K * W`

Source: `paper/main.tex:1212–1216`, the first convolution `K * W` inside `h := ζ * tanh(K * W)`.
For a fixed smooth compact kernel `K`, the finite families `(K * W)(h + xⱼ)ⱼ` and
`(K * W)(xⱼ)ⱼ` have the same law. The proof uses only the cited generic white-noise
characteristic functional `hwhite`, samplewise linearity of the distribution `W ω`, and
Lebesgue translation invariance of the squared L² mass of a finite test sum.

No stationarity is assumed. Finite laws are compared through the dual characteristic
functional `Measure.ext_of_charFunDual`, so no inner-product structure is imposed on the
source space `Vec d`. This is stationarity of raw finite-dimensional laws only. The final
stationary field `h`, its physical coefficient law, and the finite-range construction need a
later measurable-field transport. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Evaluation of a finite sum of actual test functions, through the additive coercion
`TestFunction.coeFnAddMonoidHom`. -/
private theorem sum_testFunction_apply {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → NoiseTest d) (y : Vec d) :
    (∑ j ∈ s, f j) y = ∑ j ∈ s, f j y := by
  have h := congrFun
    (map_sum (FunLike.coeAddMonoidHom (NoiseTest d) (Vec d) ℝ) f s) y
  rw [Finset.sum_apply] at h
  exact h

/-- A finite linear combination of reflected kernel translates, evaluated pointwise. -/
private theorem sum_kernelTest_apply {d n : ℕ} (K : NoiseTest d) (c : Fin n → ℝ)
    (ys : Fin n → Vec d) (y : Vec d) :
    (∑ j, c j • kernelTest K (ys j)) y = ∑ j, c j * K (ys j - y) := by
  rw [sum_testFunction_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- Expansion of a continuous linear functional on `Fin n → ℝ` along the coordinate vectors. -/
private theorem dual_apply_sum {n : ℕ} (L : StrongDual ℝ (Fin n → ℝ)) (v : Fin n → ℝ) :
    L v = ∑ i, v i * L (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

/-- A continuous linear functional of the vector of first-convolution values is evaluation
of the noise at one finite test sum. Samplewise linearity of `W` is the only input. -/
private theorem dual_mollifiedNoise {d n : ℕ} (W : NoiseSample d) (K : NoiseTest d)
    (L : StrongDual ℝ (Fin n → ℝ)) (ys : Fin n → Vec d) :
    L (fun j => mollifiedNoise W K (ys j)) =
      W (∑ j, L (Pi.single j (1 : ℝ) : Fin n → ℝ) • kernelTest K (ys j)) := by
  rw [dual_apply_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_smul, smul_eq_mul, mollifiedNoise]
  ring

/-- The characteristic function of one noise evaluation, read off from the cited white-noise
functional `hwhite` at frequency `r = 1`. -/
private theorem integral_exp_noise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (W : Ω → NoiseSample d)
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f : NoiseTest d) :
    (∫ ω, Complex.exp (((W ω f : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp ((((-(1 / 2 : ℝ)) * (∫ y : Vec d, (f y) ^ 2) : ℝ)) : ℂ) := by
  have hpt : ∀ ω, Complex.exp (((W ω f : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (W ω f : ℂ)) := by
    intro ω
    congr 1
    rw [Complex.ofReal_one]
    ring
  rw [integral_congr_ae (ae_of_all P hpt), hwhite f 1]
  congr 1
  push_cast
  ring

/-- Characteristic function of a continuous linear functional of the vector
`(K * W)(ys j)ⱼ`, expressed through the finite test sum `∑ⱼ L(eⱼ) • K(ys j - ·)`. -/
private theorem integral_exp_mollified_dual {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d n : ℕ} (W : Ω → NoiseSample d)
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (K : NoiseTest d) (L : StrongDual ℝ (Fin n → ℝ)) (ys : Fin n → Vec d) :
    (∫ ω, Complex.exp (((L (fun j => mollifiedNoise (W ω) K (ys j)) : ℝ) : ℂ) * Complex.I)
        ∂P) =
      Complex.exp ((((-(1 / 2 : ℝ)) *
        (∫ y : Vec d, (∑ j, L (Pi.single j (1 : ℝ) : Fin n → ℝ) * K (ys j - y)) ^ 2) : ℝ)) : ℂ) := by
  have hpt : ∀ ω : Ω,
      Complex.exp (((L (fun j => mollifiedNoise (W ω) K (ys j)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((W ω (∑ j, L (Pi.single j (1 : ℝ) : Fin n → ℝ) • kernelTest K (ys j)) :
          ℝ) : ℂ) * Complex.I) := by
    intro ω
    rw [dual_mollifiedNoise]
  calc (∫ ω, Complex.exp (((L (fun j => mollifiedNoise (W ω) K (ys j)) : ℝ) : ℂ) * Complex.I)
        ∂P)
      = ∫ ω, Complex.exp (((W ω (∑ j, L (Pi.single j (1 : ℝ) : Fin n → ℝ) •
          kernelTest K (ys j)) : ℝ) : ℂ) * Complex.I) ∂P :=
        integral_congr_ae (ae_of_all P hpt)
    _ = Complex.exp ((((-(1 / 2 : ℝ)) *
          (∫ y : Vec d, ((∑ j, L (Pi.single j (1 : ℝ) : Fin n → ℝ) • kernelTest K (ys j)) y) ^ 2) :
          ℝ)) : ℂ) :=
        integral_exp_noise P W hwhite _
    _ = Complex.exp ((((-(1 / 2 : ℝ)) *
          (∫ y : Vec d, (∑ j, L (Pi.single j (1 : ℝ) : Fin n → ℝ) * K (ys j - y)) ^ 2) : ℝ)) :
          ℂ) := by
        simp only [sum_kernelTest_apply]

/-- Lebesgue translation invariance of the squared L² mass of a finite kernel sum. The shift
`y ↦ y - h` is the actual Lebesgue translation on `Vec d = Fin d → ℝ`. -/
private theorem integral_sq_sum_translate {d n : ℕ} (K : NoiseTest d) (c : Fin n → ℝ)
    (xs : Fin n → Vec d) (h : Vec d) :
    (∫ y : Vec d, (∑ j, c j * K (h + xs j - y)) ^ 2) =
      ∫ y : Vec d, (∑ j, c j * K (xs j - y)) ^ 2 := by
  have hshift : ∀ y : Vec d, (∑ j, c j * K (h + xs j - y)) ^ 2 =
      (∑ j, c j * K (xs j - (y - h))) ^ 2 := by
    intro y
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show h + xs j - y = xs j - (y - h) by abel]
  calc (∫ y : Vec d, (∑ j, c j * K (h + xs j - y)) ^ 2)
      = ∫ y : Vec d, (∑ j, c j * K (xs j - (y - h))) ^ 2 :=
        integral_congr_ae (ae_of_all volume hshift)
    _ = ∫ y : Vec d, (∑ j, c j * K (xs j - y)) ^ 2 :=
        integral_sub_right_eq_self (μ := volume)
          (fun y : Vec d => (∑ j, c j * K (xs j - y)) ^ 2) h

/-- **Stationarity of the raw finite-dimensional laws of the first convolution.**
Source: `paper/main.tex:1212–1216`. For every compact kernel `K`, finite family `xs`, and shift
`h`, the vectors `((K * W)(h + xⱼ))ⱼ` and `((K * W)(xⱼ))ⱼ` are identically distributed under
`P`. The hypothesis `hwhite` is the cited generic white-noise characteristic functional. -/
theorem identDistrib_mollifiedNoise_translate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (K : NoiseTest d) (n : ℕ) (xs : Fin n → Vec d) (h : Vec d) :
    ProbabilityTheory.IdentDistrib
      (fun ω => fun j : Fin n => mollifiedNoise (W ω) K (h+xs j))
      (fun ω => fun j : Fin n => mollifiedNoise (W ω) K (xs j)) P P := by
  have hF : Measurable (fun ω => fun j : Fin n => mollifiedNoise (W ω) K (h + xs j)) :=
    Measurable.of_eval fun j => measurable_mollifiedNoise W hmeas K (h + xs j)
  have hG : Measurable (fun ω => fun j : Fin n => mollifiedNoise (W ω) K (xs j)) :=
    Measurable.of_eval fun j => measurable_mollifiedNoise W hmeas K (xs j)
  refine ⟨hF.aemeasurable, hG.aemeasurable, ?_⟩
  apply Measure.ext_of_charFunDual
  funext L
  have hcont : Continuous fun v : Fin n → ℝ => Complex.exp (((L v : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  rw [charFunDual_apply, charFunDual_apply,
    integral_map hF.aemeasurable hcont.aestronglyMeasurable,
    integral_map hG.aemeasurable hcont.aestronglyMeasurable,
    integral_exp_mollified_dual P W hwhite K L (fun j => h + xs j),
    integral_exp_mollified_dual P W hwhite K L xs,
    integral_sq_sum_translate K (fun j => L (Pi.single j (1 : ℝ) : Fin n → ℝ)) xs h]

end EinsteinRelation.Sharpness
