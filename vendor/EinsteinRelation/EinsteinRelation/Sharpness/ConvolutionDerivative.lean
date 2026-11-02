import EinsteinRelation.Sharpness.Fields
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Support

/-! # Deterministic coordinate derivatives of the outer convolution

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1216. For a smooth,
compactly supported `ζ` and a continuous `H`, the coordinate derivative of the Lebesgue outer
convolution `z ↦ ∫ ζ(y) H(z - y) dy` falls on the kernel `ζ`. The amplitude bound `|H| ≤ 1`
then bounds it by the `L¹` norm of the coordinate derivative of `ζ`, with no derivative of `H`
assumed. The results are deterministic: no stationarity, finite range, or Gaussian law is used.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Sharpness

/-- Lebesgue measure on `Vec d` is invariant under negation. The pinned Mathlib has no
`Measure.IsNegInvariant` instance for Haar measures. Negation is the linear map `(-1) • id`, whose
determinant `(-1) ^ d` has absolute value one, so the pushforward rescales the measure by one. -/
private instance isNegInvariant_volume (d : ℕ) :
    Measure.IsNegInvariant (volume : Measure (Vec d)) := by
  refine ⟨?_⟩
  have hdet : LinearMap.det ((-1 : ℝ) • (LinearMap.id : Vec d →ₗ[ℝ] Vec d)) = (-1) ^ d := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fin_fun ℝ]
  have hdetne : LinearMap.det ((-1 : ℝ) • (LinearMap.id : Vec d →ₗ[ℝ] Vec d)) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ (by norm_num)
  have hf : ⇑((-1 : ℝ) • (LinearMap.id : Vec d →ₗ[ℝ] Vec d)) = (Neg.neg : Vec d → Vec d) := by
    funext v
    simp
  show Measure.map (Neg.neg : Vec d → Vec d) (volume : Measure (Vec d)) = volume
  rw [← hf, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdetne, hdet]
  simp [abs_inv, abs_pow]

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216. For a smooth, compactly
supported `ζ` and a continuous `H`, the coordinate derivative of the outer convolution
`z ↦ ∫ ζ(y) H(z - y) dy` is the outer convolution of the coordinate derivative of `ζ` with `H`. -/
theorem coordinateDerivative_outer_convolution {d : ℕ} (ζ H : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hH : Continuous H)
    (i : Fin d) (x : Vec d) :
    coordinateDerivative i (fun z : Vec d => ∫ y : Vec d, ζ y * H (z-y)) x =
      ∫ y : Vec d, coordinateDerivative i ζ y * H (x-y) := by
  have hfun : (fun z : Vec d => ∫ y : Vec d, ζ y * H (z-y)) =
      ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H := by
    funext z
    simp only [convolution_lsmul, smul_eq_mul]
  -- The derivative of the convolution moves onto `ζ`, which needs `C¹` with compact support.
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (mod_cast le_top)
  have hderiv : HasFDerivAt (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H)
      ((fderiv ℝ ζ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d), volume] H) x) x :=
    HasCompactSupport.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hζc hζ1
      hH.locallyIntegrable x
  have hDc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv (by simp)
  have hcont : Continuous (fun y : Vec d => x - y) := continuous_const.sub continuous_id
  have hHc : Continuous (fun t : Vec d => H (x - t)) := hH.comp hcont
  -- The kernel `t ↦ H (x - t) • fderiv ζ t` is continuous with compact support, so integrable.
  have hcs : HasCompactSupport (fun t : Vec d => H (x - t) • fderiv ℝ ζ t) :=
    (hζc.fderiv ℝ).smul_left (f := fun t : Vec d => H (x - t))
  have hint : Integrable (fun t : Vec d => H (x - t) • fderiv ℝ ζ t) volume :=
    (hHc.smul hDc).integrable_of_hasCompactSupport hcs
  -- The `precompL` kernel of the scalar `lsmul` is the scalar multiple `H (x - t) • fderiv ζ t`.
  have hφ : (fun t : Vec d =>
      (ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d) (fderiv ℝ ζ t) (H (x - t))) =
      fun t : Vec d => H (x - t) • fderiv ℝ ζ t := by
    funext t
    ext v
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  unfold coordinateDerivative
  rw [hfun, hderiv.fderiv, convolution_def, hφ, ContinuousLinearMap.integral_apply hint]
  congr 1
  funext t
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216. If `|H| ≤ 1`, the
coordinate derivative of the outer convolution `z ↦ ∫ ζ(y) H(z - y) dy` is bounded pointwise by
the `L¹` norm of the coordinate derivative of `ζ`. The bound uses no derivative of `H`. -/
theorem abs_coordinateDerivative_outer_convolution_le {d : ℕ} (ζ H : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hH : Continuous H)
    (hb : ∀ x, |H x| ≤ 1) (i : Fin d) (x : Vec d) :
    |coordinateDerivative i (fun z : Vec d => ∫ y : Vec d, ζ y * H (z-y)) x| ≤
      ∫ y : Vec d, |coordinateDerivative i ζ y| := by
  -- The coordinate derivative of `ζ` is continuous with compact support, hence integrable.
  have hkC : Continuous (fun y : Vec d => coordinateDerivative i ζ y) := by
    unfold coordinateDerivative
    exact (hζ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hkc : HasCompactSupport (fun y : Vec d => coordinateDerivative i ζ y) :=
    hζc.fderiv_apply ℝ (unitVector i)
  have hkInt : Integrable (fun y : Vec d => coordinateDerivative i ζ y) volume :=
    hkC.integrable_of_hasCompactSupport hkc
  have hcont : Continuous (fun y : Vec d => x - y) := continuous_const.sub continuous_id
  have hprodCont : Continuous (fun y : Vec d => coordinateDerivative i ζ y * H (x - y)) :=
    hkC.mul (hH.comp hcont)
  have hprodComp : HasCompactSupport (fun y : Vec d => coordinateDerivative i ζ y * H (x - y)) :=
    hkc.mul_right
  have hprodInt : Integrable (fun y : Vec d => coordinateDerivative i ζ y * H (x - y)) volume :=
    hprodCont.integrable_of_hasCompactSupport hprodComp
  have hpt : ∀ y : Vec d, ‖coordinateDerivative i ζ y * H (x - y)‖ ≤
      |coordinateDerivative i ζ y| := fun y => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hb _)
  rw [coordinateDerivative_outer_convolution ζ H hζ hζc hH i x]
  calc |∫ y : Vec d, coordinateDerivative i ζ y * H (x - y)|
      = ‖∫ y : Vec d, coordinateDerivative i ζ y * H (x - y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y : Vec d, ‖coordinateDerivative i ζ y * H (x - y)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : Vec d, |coordinateDerivative i ζ y| :=
        integral_mono hprodInt.norm hkInt.abs hpt

end EinsteinRelation.Sharpness
