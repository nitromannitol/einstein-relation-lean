import EinsteinRelation.Correctors.AKMHeatKernelGaussianData

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Positive Gaussian weights are integrable on the coordinate carrier.
Source: AKM E.1 (E.7); `paper/main.tex:777–784,842`. -/
theorem integrable_scaled_gaussian_origin {d : ℕ} {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) volume := by
  have h_sqrt_pos : Real.sqrt κ ≠ 0 := Real.sqrt_pos.mpr hκ |>.ne'
  have h_base : Integrable (fun x : Vec d => Real.exp (-euclideanSq x)) volume := by
    have := integrable_gaussian_kernel (0 : Vec d)
    simpa [sub_zero] using this
  have h_sq_sqrt : (Real.sqrt κ) ^ 2 = κ := Real.sq_sqrt hκ.le
  have h_eq : (fun x : Vec d => Real.exp (-κ * euclideanSq x)) =
      (fun x : Vec d => Real.exp (-euclideanSq x)) ∘ (Real.sqrt κ • ·) := by
    ext x
    dsimp
    have h1 : κ * euclideanSq x = euclideanSq (Real.sqrt κ • x) := by
      calc
        κ * euclideanSq x = ((Real.sqrt κ) ^ 2) * euclideanSq x := by rw [h_sq_sqrt]
        _ = (Real.sqrt κ) ^ 2 * (∑ i, x i * x i) := rfl
        _ = ∑ i, (Real.sqrt κ) ^ 2 * (x i * x i) := by rw [Finset.mul_sum]
        _ = ∑ i, ((Real.sqrt κ) * x i) * ((Real.sqrt κ) * x i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        _ = euclideanSq (Real.sqrt κ • x) := rfl
    simp [h1]
  rw [h_eq]
  exact h_base.comp_smul h_sqrt_pos

end EinsteinRelation.Correctors
