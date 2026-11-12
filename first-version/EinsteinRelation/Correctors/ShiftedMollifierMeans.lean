import EinsteinRelation.Correctors.SpatialWeakProduct
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Translation of smooth corrector averages

Source: `paper/main.tex:948–955`. A corrector has only a weak spatial
gradient. Its smooth averages are nevertheless differentiable, and their
translation difference is the integral of the tested gradient along the
translation segment. No pointwise differentiability of the corrector is used.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

private theorem translatedTest {d : ℕ} {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (x : Vec d) :
    IsSpatialTest Set.univ (fun z => ζ (x - z)) := by
  refine ⟨hζ.comp (contDiff_const.sub contDiff_id), ?_, Set.subset_univ _⟩
  exact hζc.comp_homeomorph (Homeomorph.subLeft x)

private theorem coordinateDerivative_translatedTest {d : ℕ} {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (x z : Vec d) (j : Fin d) :
    coordinateDerivative j (fun w => ζ (x - w)) z =
      -coordinateDerivative j ζ (x - z) := by
  have h := ((hζ.differentiable (mod_cast le_top) (x - z)).hasFDerivAt).comp z
    ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
  dsimp only [Function.comp_def] at h
  change fderiv ℝ (fun w => ζ (x - w)) z (unitVector j) = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg, coordinateDerivative]

/-- The derivative of a smooth average can be transferred from its
mollifier to an actual weak derivative of the averaged field.
Source: `paper/main.tex:948–955`. -/
theorem convolution_coordinateDerivative_eq_weakDerivative {d : ℕ}
    {f g ζ : Vec d → ℝ} {j : Fin d}
    (hfg : HasWeakPartialDerivative Set.univ j f g)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (x : Vec d) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] coordinateDerivative j ζ) x =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) x := by
  have h := hfg.2.2 _ (translatedTest hζ hζc x)
  simp only [Measure.restrict_univ, coordinateDerivative_translatedTest hζ,
    mul_neg, integral_neg, neg_inj] at h
  exact h

/-- The derivative of the smooth scalar average along a translation
segment equals the directional average of its weak gradient.
Source: `paper/main.tex:948–955`. -/
theorem hasDerivAt_convolution_segment {d : ℕ}
    {f ζ : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : LocallyIntegrable f volume)
    (hG : HasWeakGradient Set.univ f G)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (y : Vec d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) (s • y))
      (∑ j : Fin d, y j * ((fun z => G z j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ)
        (t • y)) t := by
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (mod_cast le_top)
  have hD := (hζc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hf hζ1 (t • y)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const y)
  simp only [one_smul, Function.comp_def, id_eq] at hD
  have hcoord (j : Fin d) :
      ((f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Vec d), volume]
        fderiv ℝ ζ) (t • y)) (unitVector j) =
        ((fun z => G z j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) (t • y) := by
    rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
      hf (hζc.fderiv ℝ) (hζ1.continuous_fderiv le_rfl)]
    exact convolution_coordinateDerivative_eq_weakDerivative (hG j) hζ hζc _
  have hy : y = ∑ j : Fin d, y j • unitVector j := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVector,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hval :
      ((f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Vec d), volume]
        fderiv ℝ ζ) (t • y)) y =
      ∑ j : Fin d, y j * ((fun z => G z j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ)
        (t • y) := by
    calc
      _ = ((f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Vec d), volume]
        fderiv ℝ ζ) (t • y)) (∑ j : Fin d, y j • unitVector j) := congrArg _ hy
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, hcoord]
  rwa [hval] at hD

/-- The shifted mean is exactly a segment integral of tested gradients.
This justifies the fundamental-theorem step for Sobolev correctors and for
each scalar entry of the skew corrector. Source: `paper/main.tex:948–955`. -/
theorem convolution_shift_sub_eq_integral_weakGradient {d : ℕ}
    {f ζ : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : LocallyIntegrable f volume)
    (hG : HasWeakGradient Set.univ f G)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (y : Vec d) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) y -
        (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) 0 =
      ∫ t in (0 : ℝ)..1, ∑ j : Fin d,
        y j * ((fun z => G z j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) (t • y) := by
  have hc : Continuous (fun t : ℝ => ∑ j : Fin d,
      y j * ((fun z => G z j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) (t • y)) := by
    apply continuous_finset_sum
    intro j _
    have hGj : LocallyIntegrable (fun z => G z j) volume := by
      simpa only [locallyIntegrableOn_univ] using (hG j).2.1
    exact continuous_const.mul ((hζc.continuous_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hGj hζ.continuous).comp
        (continuous_id.smul continuous_const))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun t _ => hasDerivAt_convolution_segment hf hG hζ hζc y t) (hc.intervalIntegrable 0 1)
  simpa only [one_smul, zero_smul] using hFTC.symm

end EinsteinRelation.Correctors
