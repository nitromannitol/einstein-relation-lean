import EinsteinFull.Calculus.C20TubeNegativePowerWeakGradient
import Mathlib.MeasureTheory.Function.L2Space

open EinsteinRelation MeasureTheory
open PDE hiding Vec Mat

namespace EinsteinFull.Calculus

/-- A positive lower bound controls the negative-power gradient energy. -/
theorem c20_negative_power_gradient_energy_integrable
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {d : ℕ}
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (G : X → Vec d) (hG : MemLp (fun x => euclideanNorm (G x)) 2 μ)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hpos : ∀ᵐ x ∂μ, ε ≤ u x) :
    Integrable (fun x => Real.rpow (u x) (-p-2) * euclideanSq (G x)) μ := by
  have hn (x : X) : euclideanNorm (G x) ^ 2 = euclideanSq (G x) := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (G x i)
  have hs : Integrable (fun x => euclideanSq (G x)) μ := by
    simpa only [hn] using hG.integrable_sq
  apply (hs.const_mul (Real.rpow ε (-p-2))).mono'
  · exact (hu.aemeasurable.pow_const (-p-2)).aestronglyMeasurable.mul hs.1
  · filter_upwards [hpos] with x hx
    have hs0 : 0 ≤ euclideanSq (G x) := by rw [← hn]; positivity
    have hr0 : 0 ≤ Real.rpow (u x) (-p-2) := Real.rpow_nonneg (le_trans hε.le hx) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr0 hs0)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hε hx (by linarith)) hs0

end EinsteinFull.Calculus
