import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Actual test kernels for a generic distribution-valued white noise

AKM Definition5.1, Proposition5.14 and Remark5.15 provide a candidate generic
white-noise input, not the paper's sharpness construction. No such input is frozen
or assumed here. The present deterministic definitions use Mathlib's actual LF
test functions and continuous linear distributions. In particular, samplewise
linearity concerns compact smooth tests, never all L² tests.

The manuscript's first convolution `K * W` (`paper/main.tex:1212–1216`) evaluates a
distribution on the reflected translate `y ↦ K(x-y)`. Gaussian laws, stationarity,
finite range, outer smoothing and nondegeneracy remain separate obligations.
-/

open MeasureTheory
open scoped Distributions

namespace EinsteinRelation.Sharpness

/-- Actual smooth compactly supported scalar tests on the coordinate space. -/
abbrev NoiseTest (d : ℕ) := TestFunction (⊤ : TopologicalSpace.Opens (Vec d)) ℝ ⊤

/-- Actual scalar distributions on the LF test-function space. -/
abbrev NoiseSample (d : ℕ) := Distribution (⊤ : TopologicalSpace.Opens (Vec d)) ℝ ⊤

/-- The reflected translate of the actual smoothing kernel, as a compact test. -/
noncomputable def kernelTest {d : ℕ} (K : NoiseTest d) (x : Vec d) : NoiseTest d where
  toFun := fun y => K (x - y)
  contDiff' := K.contDiff.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := K.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft x)
  tsupport_subset' := Set.subset_univ _

@[simp] theorem kernelTest_apply {d : ℕ} (K : NoiseTest d) (x y : Vec d) :
    kernelTest K x y = K (x - y) := rfl

/-- The first convolution, defined by genuine distribution evaluation. -/
noncomputable def mollifiedNoise {d : ℕ} (W : NoiseSample d) (K : NoiseTest d)
    (x : Vec d) : ℝ := W (kernelTest K x)

theorem kernelTest_smul_add {d : ℕ} (c : ℝ) (K H : NoiseTest d) (x : Vec d) :
    kernelTest (c • K + H) x = c • kernelTest K x + kernelTest H x := by
  ext y
  rfl

/-- Simultaneous samplewise linearity on the legitimate compact test carrier. -/
theorem mollifiedNoise_smul_add_test {d : ℕ} (W : NoiseSample d) (c : ℝ)
    (K H : NoiseTest d) (x : Vec d) :
    mollifiedNoise W (c • K + H) x =
      c * mollifiedNoise W K x + mollifiedNoise W H x := by
  unfold mollifiedNoise
  rw [kernelTest_smul_add, map_add, map_smul]
  rfl

/-- The variance of a translated kernel is exactly its fixed L² mass. -/
theorem kernelTest_l2_mass {d : ℕ} (K : NoiseTest d) (x : Vec d) :
    (∫ y : Vec d, (kernelTest K x y) ^ 2) = ∫ y : Vec d, (K y) ^ 2 :=
  integral_sub_left_eq_self (fun y : Vec d => (K y) ^ 2) volume x

/-- Fixed-point measurability follows from measurable distribution evaluations;
no Borel measurability of the strong dual itself is required. -/
theorem measurable_mollifiedNoise {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (K : NoiseTest d) (x : Vec d) :
    Measurable (fun ω => mollifiedNoise (W ω) K x) :=
  hmeas (kernelTest K x)

/-- A generic unit-variance Gaussian distribution contract has a real convolution
consumer: the smoothed characteristic function has the kernel's fixed L² mass. This is conditional
on the generic noise characteristic law, not an external assumption about `h`. -/
theorem mollifiedNoise_characteristic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1 / 2 : ℝ)) * r ^ 2 * ∫ y : Vec d, (f y) ^ 2) : ℂ))
    (K : NoiseTest d) (x : Vec d) (r : ℝ) :
    (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (mollifiedNoise (W ω) K x : ℂ)) ∂P) =
      Complex.exp (((-(1 / 2 : ℝ)) * r ^ 2 * ∫ y : Vec d, (K y) ^ 2) : ℂ) := by
  change (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω (kernelTest K x) : ℂ)) ∂P) = _
  rw [hwhite, kernelTest_l2_mass]

end EinsteinRelation.Sharpness
