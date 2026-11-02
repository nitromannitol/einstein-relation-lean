import EinsteinRelation.Calculus.Mollifier
import EinsteinRelation.External.WhiteNoise

/-! # A concrete kernel for the first sharpness convolution

The kernel is the actual nonnegative smooth compact unit-mass function fixed in
`paper/main.tex:753`, used as the nonzero `K` in1212–1216. The bounded nonlinear
and outer convolutions, joint finite range and nondegeneracy remain internal.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- The constructed unit-mass function as an actual distribution test. -/
noncomputable def mollifierNoiseTest (d : ℕ) : NoiseTest d where
  toFun := mollifier d
  contDiff' := contDiff_mollifier d
  hasCompactSupport' := hasCompactSupport_mollifier d
  tsupport_subset' := Set.subset_univ _

@[simp] theorem mollifierNoiseTest_apply (d : ℕ) (x : Vec d) :
    mollifierNoiseTest d x = mollifier d x := rfl

theorem mollifierNoiseTest_ne_zero (d : ℕ) : mollifierNoiseTest d ≠ 0 := by
  intro h
  have hz (x : Vec d) : mollifier d x = 0 :=
    congrArg (fun f : NoiseTest d => f x) h
  have hm := integral_mollifier d
  simp only [hz, integral_zero] at hm
  exact zero_ne_one hm

/-- A concrete first convolution under the frozen generic existence hypothesis.
One actual distribution law supplies all points and all Fourier parameters. -/
theorem exists_mollifier_convolution {d : ℕ} (h : External.WhiteNoiseExistence d) :
    ∃ P : Measure (NoiseSample d), External.IsWhiteNoiseLaw P ∧ ∀ x : Vec d,
      Measurable (fun W : NoiseSample d => mollifiedNoise W (mollifierNoiseTest d) x) ∧
      ∀ r : ℝ,
        (∫ W, Complex.exp (Complex.I * (r : ℂ) *
            (mollifiedNoise W (mollifierNoiseTest d) x : ℂ)) ∂P) =
          Complex.exp (((-(1 / 2 : ℝ)) * r ^ 2 * ∫ y : Vec d, (mollifier d y) ^ 2) : ℂ) :=
  h.has_mollifiedNoise (mollifierNoiseTest d)

end EinsteinRelation.Sharpness
