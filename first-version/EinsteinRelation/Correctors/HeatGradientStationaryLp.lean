import EinsteinRelation.Correctors.HeatGradientConvolution

/-!
# Stationary moment bounds for the source heat-gradient integral

Source: `paper/main.tex:722,756`. The actual spatial heat integral has the
same finite-moment estimate as its two stationary Hessian convolutions.
Spatial integrability is proved before identifying these integrals.
-/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Each mixed Gaussian Hessian is continuous at positive time. -/
theorem continuous_heatKernel_mixedHessian {d : ℕ} (t : ℝ) (ht : 0 < t)
    (i j : Fin d) :
    Continuous (coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) t))) := by
  have heq := funext (coordinateDerivative_two_euclideanHeatKernel t ht i j)
  rw [heq]
  exact ((contDiff_euclideanHeatKernel t).continuous).mul
    (((continuous_apply i).mul (continuous_apply j)).div_const _ |>.sub continuous_const)

/-- The two actual Hessian integrands are integrable along almost every
stationary orbit. -/
theorem ae_integrable_heatGradient_mixedHessian {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d)
    (hKj : Integrable (coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t))) volume)
    (hKk : Integrable (coordinateDerivative l (coordinateDerivative k
      (euclideanHeatKernel (d := d) t))) volume)
    (hFj : Integrable (fun ω => F ω j) Q)
    (hFk : Integrable (fun ω => F ω k) Q) :
    ∀ᵐ ρ ∂Q,
      Integrable (fun y : Vec d => F (translate y ρ) k *
        coordinateDerivative l (coordinateDerivative j
          (euclideanHeatKernel (d := d) t)) (-y)) volume ∧
      Integrable (fun y : Vec d => F (translate y ρ) j *
        coordinateDerivative l (coordinateDerivative k
          (euclideanHeatKernel (d := d) t)) (-y)) volume := by
  have hmj := (continuous_heatKernel_mixedHessian t ht j l).comp continuous_neg
  have hmk := (continuous_heatKernel_mixedHessian t ht k l).comp continuous_neg
  filter_upwards [ae_integrable_kernel_translate hQ hmj.measurable hKj.comp_neg
      ((measurable_pi_apply k).comp hF) hFk,
    ae_integrable_kernel_translate hQ hmk.measurable hKk.comp_neg
      ((measurable_pi_apply j).comp hF) hFj] with ρ hk hj
  exact ⟨by simpa only [Function.comp_apply, mul_comm] using hk,
    by simpa only [Function.comp_apply, mul_comm] using hj⟩

/-- The moment of the literal spatial heat integral is bounded by the
`L¹` masses of its mixed Hessians and the moments of the source coordinates.
No change of heat cutoff or interchange of time integrals is used here. -/
theorem eLpNorm_heatGradientSpaceIntegral_le {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d)
    (hKj : Integrable (coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t))) volume)
    (hKk : Integrable (coordinateDerivative l (coordinateDerivative k
      (euclideanHeatKernel (d := d) t))) volume)
    (hFj : Integrable (fun ω => F ω j) Q)
    (hFk : Integrable (fun ω => F ω k) Q) :
    eLpNorm (fun ρ => akmHeatGradientSpaceIntegral
      (fun y => F (translate y ρ)) t j k l 0) p Q ≤
      ENNReal.ofReal (∫ y, |coordinateDerivative l (coordinateDerivative j
        (euclideanHeatKernel (d := d) t)) y|) * eLpNorm (fun ρ => F ρ k) p Q +
      ENNReal.ofReal (∫ y, |coordinateDerivative l (coordinateDerivative k
        (euclideanHeatKernel (d := d) t)) y|) * eLpNorm (fun ρ => F ρ j) p Q := by
  let Kj : Vec d → ℝ := fun y => coordinateDerivative l (coordinateDerivative j
    (euclideanHeatKernel (d := d) t)) (-y)
  let Kk : Vec d → ℝ := fun y => coordinateDerivative l (coordinateDerivative k
    (euclideanHeatKernel (d := d) t)) (-y)
  have hmj : Measurable Kj :=
    ((continuous_heatKernel_mixedHessian t ht j l).comp continuous_neg).measurable
  have hmk : Measurable Kk :=
    ((continuous_heatKernel_mixedHessian t ht k l).comp continuous_neg).measurable
  have hfjm := (measurable_pi_apply j).comp hF
  have hfkm := (measurable_pi_apply k).comp hF
  have heq : (fun ρ => akmHeatGradientSpaceIntegral
      (fun y => F (translate y ρ)) t j k l 0) =ᵐ[Q]
      (fun ρ => horizontalMollify Kj (fun ω => F ω k) ρ -
        horizontalMollify Kk (fun ω => F ω j) ρ) := by
    filter_upwards [ae_integrable_heatGradient_mixedHessian hQ F hF t ht j k l
      hKj hKk hFj hFk] with ρ hρ
    exact akmHeatGradientSpaceIntegral_eq_horizontalMollify F ρ t ht j k l hρ.1 hρ.2
  rw [eLpNorm_congr_ae heq]
  have hsub := eLpNorm_sub_le (μ := Q)
    (measurable_horizontalMollify Kj hmj hfkm).aestronglyMeasurable
    (measurable_horizontalMollify Kk hmk hfjm).aestronglyMeasurable hp
  refine hsub.trans ?_
  have hbj := eLpNorm_horizontalMollify_le hQ hp hpt hmj hKj.comp_neg hfkm
  have hbk := eLpNorm_horizontalMollify_le hQ hp hpt hmk hKk.comp_neg hfjm
  have hIj : (∫ y, |Kj y|) = ∫ y, |coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t)) y| :=
    integral_neg_eq_self (fun y : Vec d => |coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t)) y|) volume
  have hIk : (∫ y, |Kk y|) = ∫ y, |coordinateDerivative l (coordinateDerivative k
      (euclideanHeatKernel (d := d) t)) y| :=
    integral_neg_eq_self (fun y : Vec d => |coordinateDerivative l (coordinateDerivative k
      (euclideanHeatKernel (d := d) t)) y|) volume
  rw [hIj] at hbj
  rw [hIk] at hbk
  exact add_le_add hbj hbk

end EinsteinRelation.Correctors
