import EinsteinFull.Calculus.S4DivisionKernel
import EinsteinFull.Frozen.ProfileTaylorCoefficient

/-!
# The index-zero integrated kernel coefficient is the plain correlation integral
-/

open MeasureTheory Set

namespace EinsteinFull

theorem profileTaylorCoefficient_zero (u₀ u₂ γ : ℝ) : profileTaylorCoefficient u₀ u₂ γ 0 = u₀ := by
  simp [profileTaylorCoefficient, gaussianProfile]

theorem kernelProfileRemainder_re_zero (d : ℕ) (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ) (t : ℝ) :
    (kernelProfileRemainder d u₀ u₂ γ K t ((0 : ℝ) : ℂ)).re =
      (K t 0).re - if 1 ≤ t then t ^ (-1 - (d : ℝ) / 2) * u₀ else 0 := by
  unfold kernelProfileRemainder
  by_cases h : 1 ≤ t
  · simp [h, complexGaussianProfile]
  · simp [h]

theorem integrated_kernel_zero {d : ℕ} (hd : 1 ≤ d) (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
    (hint : IntegrableOn (fun t : ℝ => (K t 0).re) (Ici (0 : ℝ))) :
    (∫ t in Ici (0 : ℝ), iteratedDeriv 0 (fun lam : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 / (((0 : ℕ).factorial : ℕ) : ℝ)) +
      2 * profileTaylorCoefficient u₀ u₂ γ 0 / (((d - 0 : ℕ)) : ℝ) =
        ∫ t in Ici (0 : ℝ), (K t 0).re := by
  have h := integral_remainder_add hd u₀ hint
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    kernelProfileRemainder_re_zero, profileTaylorCoefficient_zero, Nat.sub_zero]
  exact h

end EinsteinFull
