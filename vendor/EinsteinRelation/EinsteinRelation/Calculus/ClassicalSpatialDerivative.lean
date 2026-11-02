import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory

namespace EinsteinRelation

/-- Classical C¹ derivatives satisfy the compact-test weak equation,
as needed for `paper/main.tex:693-698`. -/
theorem hasWeakPartialDerivative_of_contDiff {d : ℕ} (i : Fin d)
    (f : Vec d → ℝ) (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDerivative Set.univ i f (coordinateDerivative i f) := by
  have hf_cont : Continuous f := hf.continuous
  have hf_diff : Differentiable ℝ f :=
    hf.differentiable one_ne_zero
  have hfderiv_cont : Continuous (fun x => coordinateDerivative i f x) := by
    change Continuous (fun x => fderiv ℝ f x (unitVector i))
    exact (hf.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  have hf_loc : LocallyIntegrableOn f Set.univ volume :=
    locallyIntegrableOn_univ.mpr hf_cont.locallyIntegrable
  have hfderiv_loc : LocallyIntegrableOn (fun x => coordinateDerivative i f x) Set.univ volume :=
    locallyIntegrableOn_univ.mpr hfderiv_cont.locallyIntegrable
  refine ⟨hf_loc, hfderiv_loc, ?_⟩
  intro φ hφ
  have hφ_cont : Continuous φ := hφ.1.continuous
  have hφ_diff : Differentiable ℝ φ :=
    hφ.1.differentiable (by simp)
  have hφderiv_cont : Continuous (fun x => coordinateDerivative i φ x) := by
    change Continuous (fun x => fderiv ℝ φ x (unitVector i))
    exact (hφ.1.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hφderiv_c : HasCompactSupport (fun x => coordinateDerivative i φ x) :=
    hφ.2.1.fderiv_apply ℝ (unitVector i)
  have hfirst : Integrable (fun x => coordinateDerivative i f x * φ x) :=
    (hfderiv_cont.mul hφ_cont).integrable_of_hasCompactSupport
      (hφ.2.1.mul_left)
  have hsecond : Integrable (fun x => f x * coordinateDerivative i φ x) :=
    (hf_cont.mul hφderiv_cont).integrable_of_hasCompactSupport
      (hφderiv_c.mul_left)
  have hproduct : Integrable (fun x => f x * φ x) :=
    (hf_cont.mul hφ_cont).integrable_of_hasCompactSupport
      (hφ.2.1.mul_left)
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) hfirst hsecond hproduct (fun x _ => hf_diff x) (fun x _ => hφ_diff x)
  simpa [coordinateDerivative] using hparts

end EinsteinRelation
