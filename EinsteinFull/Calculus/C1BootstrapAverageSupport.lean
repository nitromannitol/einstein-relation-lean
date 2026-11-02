import EinsteinFull.Blueprint.G2.Proofs.W4BootstrapPoint
import EinsteinFull.Work.W4.ActualHomogeneousGaussianSemigroupProof

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull
open EinsteinRelation

/-- The homogeneous part of the averaged bootstrap has precisely the Gaussian
kernel mass as its Lp factor. In particular no fixed multiplicative loss is
introduced before absorbing the imaginary-force growth in the time weight. -/
theorem bootstrap_average_homogeneous_Lp {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (p : ℝ) (hp : 2 ≤ p)
    (f : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
    MemLp (homogeneousAverage Q i s hs ζ f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (homogeneousAverage Q i s hs ζ f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      Real.exp (ζ.im ^ 2 * s * homogenizedCoefficient Q i i / 2) *
        (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  have hk : Continuous (homogenizedGaussianKernel Q i s hs ζ) := by
    unfold homogenizedGaussianKernel
    fun_prop
  have h := Blueprint.bootstrap_point_kernel_Lp Q p hp
    (homogenizedGaussianKernel Q i s hs ζ) hk
    (integrable_homogenizedGaussianKernel Q i s hs ζ) f hf
  dsimp only at h
  rw [integral_norm_homogenizedGaussianKernel Q i s hs ζ] at h
  exact h

end EinsteinFull
