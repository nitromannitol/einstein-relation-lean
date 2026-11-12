import EinsteinRelation.Correctors.ParabolicSpatialIntegrationByParts
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Smooth space-time convolution retains the actual spatial gradient

Source: `paper/main.tex:832–840`. Spatial slice weak derivatives transfer
to a space-time smoothing kernel. The regularized function is genuinely
smooth even when the original solution has no temporal derivative.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A smooth compact kernel regularizes the actual L² field in space-time.
Source: `paper/main.tex:832–840`. -/
theorem paired_contDiff_spacetime_convolution {d : ℕ}
    {u κ : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) :
    ContDiff ℝ (⊤ : ℕ∞) (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ) :=
  hκc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (hu.locallyIntegrable (by norm_num)) hκ

/-- The spatial derivative of a smooth space-time convolution is the
convolution of the genuine weak spatial derivative, without any assumed
time derivative. Source: `paper/main.tex:832–840`. -/
theorem paired_convolution_spatial_fderiv {d : ℕ}
    {u κ : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : MemLp u 2 volume) (hG : ∀ j, MemLp (fun z => G z j) 2 volume)
    (hweak : ∀ᵐ t ∂(volume : Measure ℝ),
      HasWeakGradient Set.univ (fun x => u (t,x)) (fun x => G (t,x)))
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ)
    (z : ℝ × Vec d) (j : Fin d) :
    fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ) z (0,unitVector j) =
      ((fun y => G y j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ) z := by
  letI : (volume : Measure (ℝ × Vec d)).IsAddLeftInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddLeftInvariant
    infer_instance
  have htrans : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ × Vec d => κ (z-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have htransc : HasCompactSupport (fun y : ℝ × Vec d => κ (z-y)) :=
    hκc.comp_homeomorph (Homeomorph.subLeft z)
  have hder (y : ℝ × Vec d) :
      fderiv ℝ (fun w => κ (z-w)) y (0,unitVector j) =
        -fderiv ℝ κ (z-y) (0,unitVector j) := by
    have h := ((hκ.differentiable (by simp) (z-y)).hasFDerivAt).comp y
      ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
    change fderiv ℝ (κ ∘ fun w : ℝ × Vec d => z - w) y (0, unitVector j) = _
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, zero_sub,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, map_neg]
  have hibp := paired_spacetime_spatial_integration_by_parts hu hG hweak htrans htransc j
  simp only [hder, mul_neg, integral_neg, neg_inj] at hibp
  have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (mod_cast le_top)
  have hd := hκc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (hu.locallyIntegrable (by norm_num)) hκ1 z
  rw [hd.fderiv, convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    (hu.locallyIntegrable (by norm_num)) (hκc.fderiv ℝ) (hκ1.continuous_fderiv le_rfl)]
  exact hibp

end EinsteinRelation.Correctors
