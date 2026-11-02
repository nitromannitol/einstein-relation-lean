import EinsteinFull.Frozen.ComplexGaussianProfile

namespace EinsteinFull

theorem complexGaussianProfile_neg (u₀ u₂ γ : ℝ) (z : ℂ) :
    complexGaussianProfile u₀ u₂ γ (-z) = complexGaussianProfile u₀ u₂ γ z := by
  simp only [complexGaussianProfile, neg_sq]

theorem complexGaussianProfile_ofReal (u₀ u₂ γ x : ℝ) :
    complexGaussianProfile u₀ u₂ γ (x : ℂ) = (gaussianProfile u₀ u₂ γ x : ℂ) := by
  simp [complexGaussianProfile, gaussianProfile, Complex.ofReal_exp]

end EinsteinFull
