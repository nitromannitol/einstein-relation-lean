import EinsteinRelation.Correctors.LocalMollifierSpatialTest
import Mathlib.Analysis.Convolution

/-! # The literal shifted mean in Proposition 5.3

Source: `paper/main.tex:948–955`. The fixed mollifier is even, so the
printed integral defining `c_y` is the negative of the translated
convolution difference. Local integrability suffices for this identity.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

/-- Joint measurability of convolution with a continuous fixed kernel.
Source: `paper/main.tex:913–938,948–955`. -/
theorem measurable_random_convolution_joint {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → Vec d → ℝ) (hf : Measurable (Function.uncurry f))
    {ζ : Vec d → ℝ} (hζ : Continuous ζ) :
    Measurable (fun z : Vec d × Ω =>
      (f z.2 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) z.1) := by
  have hm : Measurable (fun z : (Vec d × Ω) × Vec d =>
      f z.1.2 z.2 * ζ (z.1.1 - z.2)) :=
    (hf.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
      (hζ.measurable.comp ((measurable_fst.comp measurable_fst).sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The source integral `c_y` equals the convolution at zero minus its
translate, with its exact sign and the actual even mollifier.
Source: `paper/main.tex:948–955`. -/
theorem mollifier_shift_integral_eq_convolution_sub {d : ℕ} {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) {R : ℝ} (hR : 0 < R) (y : Vec d) :
    (∫ z, (Calculus.unitMassScaledMollifier d R z -
      Calculus.unitMassScaledMollifier d R (z - y)) * f z) =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier d R) 0 -
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier d R) y := by
  let ζ := Calculus.unitMassScaledMollifier d R
  have heven (z : Vec d) : ζ (-z) = ζ z :=
    congrFun (Entropy.reflectKernel_unitMassScaledMollifier (d := d) R) z
  have hfun (x : Vec d) : (fun z => ζ (z - x) * f z) =
      (fun z => f z * ζ (x - z)) := by
    funext z
    rw [show x - z = -(z - x) by abel, heven, mul_comm]
  have hi (x : Vec d) : Integrable (fun z => ζ (z - x) * f z) volume := by
    rw [hfun]
    exact (Entropy.hasCompactSupport_unitMassScaledMollifier hR).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hf
      (Entropy.contDiff_unitMassScaledMollifier R).continuous x
  have hc (x : Vec d) :
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) x =
        ∫ z, ζ (z - x) * f z := by
    rw [hfun]
    rfl
  change (∫ z, (ζ z - ζ (z - y)) * f z) = _
  simp_rw [sub_mul]
  rw [integral_sub (by simpa using hi 0) (hi y), hc 0, hc y]
  simp only [sub_zero]

end EinsteinRelation.Correctors
