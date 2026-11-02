import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Joint coefficient averages for the test-integral sigma algebra

Source: `paper/main.tex:779–788`. Smooth coefficient averages are jointly
measurable even though point evaluation of a general source coefficient is
not an observable of its test-integral sigma algebra. Separate test-integral
measurability and spatial continuity prove the joint assertion.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- Smooth averaging of one actual coefficient entry, in source coordinates.
Source: `paper/main.tex:779–788`. -/
noncomputable def coefficientTestConvolution {d : ℕ} {K : ℝ}
    (κ : SmoothCompactTest d) (A : Coefficient d K) (x : Vec d) (i j : Fin d) : ℝ :=
  ∫ y, κ (x - y) * A y i j

/-- Every fixed-point smooth coefficient average is an allowed source
observable. Source: `paper/main.tex:779–788`. -/
theorem measurable_coefficientTestConvolution_at {d : ℕ} {K : ℝ}
    (κ : SmoothCompactTest d) (x : Vec d) (i j : Fin d) :
    Measurable (fun A : Coefficient d K => coefficientTestConvolution κ A x i j) := by
  let u : SmoothCompactTest d :=
    ⟨fun y => κ (x - y), κ.smooth.comp (contDiff_const.sub contDiff_id),
      κ.compact.comp_homeomorph (Homeomorph.subLeft x)⟩
  exact measurable_testIntegral u i j

/-- The same average uses only tests supported in its actual translated
support, giving source-local measurability. Source: `paper/main.tex:779–788`. -/
theorem measurable_coefficientTestConvolution_local {d : ℕ} {K : ℝ}
    (κ : SmoothCompactTest d) (x : Vec d) (i j : Fin d) {U : Set (Vec d)}
    (hsupp : tsupport (fun y => κ (x - y)) ⊆ U) :
    Measurable[Environment.AKMTestIntegralSupport.localSigma U]
      (fun A : Coefficient d K => coefficientTestConvolution κ A x i j) := by
  let u : {u : SmoothCompactTest d // tsupport u.toFun ⊆ U} :=
    ⟨⟨fun y => κ (x - y), κ.smooth.comp (contDiff_const.sub contDiff_id),
      κ.compact.comp_homeomorph (Homeomorph.subLeft x)⟩, hsupp⟩
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le u (le_iSup_of_le i (le_iSup_of_le j le_rfl))

/-- Spatial continuity uses local integrability of the coefficient, without
assuming joint measurability of coefficient evaluation.
Source: `paper/main.tex:779–788`. -/
theorem continuous_coefficientTestConvolution {d : ℕ} {K : ℝ}
    (κ : SmoothCompactTest d) (A : Coefficient d K) (i j : Fin d) :
    Continuous (fun x => coefficientTestConvolution κ A x i j) := by
  have h := κ.compact.continuous_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (A.locally_integrable i j) κ.smooth.continuous
  convert h using 1
  funext x
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => mul_comm _ _

/-- The actual smooth coefficient average is jointly measurable for the
source sigma algebra and spatial Borel sigma algebra.
Source: `paper/main.tex:779–788`. -/
theorem measurable_coefficientTestConvolution {d : ℕ} {K : ℝ}
    (κ : SmoothCompactTest d) (i j : Fin d) :
    Measurable (fun z : Coefficient d K × Vec d =>
      coefficientTestConvolution κ z.1 z.2 i j) := by
  exact (measurable_uncurry_of_continuous_of_measurable
    (fun A => continuous_coefficientTestConvolution κ A i j)
    (fun x => measurable_coefficientTestConvolution_at κ x i j)).comp measurable_swap

/-- Translation covariance is exact before any almost-sure version choice.
Source: `paper/main.tex:779–788`. -/
theorem coefficientTestConvolution_translate {d : ℕ} {K : ℝ}
    (κ : SmoothCompactTest d) (A : Coefficient d K) (y x : Vec d) (i j : Fin d) :
    coefficientTestConvolution κ (translateCoefficient y A) x i j =
      coefficientTestConvolution κ A (y + x) i j := by
  unfold coefficientTestConvolution
  calc
    _ = ∫ z, κ (y + x - (y + z)) * A (y + z) i j := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change κ (x - z) * A (y + z) i j =
          κ (y + x - (y + z)) * A (y + z) i j
        rw [show y + x - (y + z) = x - z by abel]
    _ = _ := integral_add_left_eq_self
      (fun z => κ (y + x - z) * A z i j) y

end EinsteinRelation.Correctors
