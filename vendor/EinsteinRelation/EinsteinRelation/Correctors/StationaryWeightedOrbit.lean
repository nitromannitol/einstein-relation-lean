import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Calculus.HorizontalSobolev
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integrating weighted stationary orbits

Source: `paper/main.tex:916–928`. Spatial averaging of stationary fields
must commute with expectation with genuine integrability. These lemmas
give that assertion on the product of spatial volume and the environment
law, without assuming samplewise boundedness of the observable.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- An integrable spatial weight times an integrable stationary observable
is integrable on the full spatial/environment product.
Source: `paper/main.tex:916–928`. -/
theorem integrable_weighted_orbit {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {a : Vec d → ℝ} {F : FieldPair d → ℝ}
    (ham : Measurable a) (ha : Integrable a volume)
    (hFm : Measurable F) (hF : Integrable F Q) :
    Integrable (fun p : Vec d × FieldPair d => a p.1 * F (translate p.1 p.2))
      (volume.prod Q) := by
  have hm : AEStronglyMeasurable
      (fun p : Vec d × FieldPair d => a p.1 * F (translate p.1 p.2)) (volume.prod Q) :=
    ((ham.comp measurable_fst).mul
    (hFm.comp Probability.continuous_translate.measurable)).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall fun x =>
    ((measurePreserving_translate Q hQ x).integrable_comp_of_integrable hF).const_mul (a x), ?_⟩
  have heq (x : Vec d) :
      (∫ ω, ‖a x * F (translate x ω)‖ ∂Q) = |a x| * ∫ ω, |F ω| ∂Q := by
    simp only [Real.norm_eq_abs, abs_mul, integral_const_mul]
    rw [Probability.integral_translate Q hQ x (fun ω => |F ω|) hFm.norm]
  simp_rw [heq]
  exact ha.abs.mul_const _

/-- Weighted stationary spatial integration commutes with expectation.
The preceding product-integrability result justifies the Fubini step.
Source: `paper/main.tex:916–928`. -/
theorem integral_weighted_orbit {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {a : Vec d → ℝ} {F : FieldPair d → ℝ}
    (ham : Measurable a) (ha : Integrable a volume)
    (hFm : Measurable F) (hF : Integrable F Q) :
    (∫ ω, ∫ x, a x * F (translate x ω) ∂volume ∂Q) =
      (∫ x, a x ∂volume) * ∫ ω, F ω ∂Q := by
  rw [integral_integral_swap (f := fun ω x => a x * F (translate x ω))
    (integrable_weighted_orbit Q hQ ham ha hFm hF).swap]
  simp_rw [integral_const_mul, Probability.integral_translate Q hQ _ F hFm]
  exact integral_mul_const _ _

end EinsteinRelation.Correctors
