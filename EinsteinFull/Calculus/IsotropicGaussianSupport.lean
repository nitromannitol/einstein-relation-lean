import EinsteinFull.Calculus.SpatialPairingSupport
import EinsteinRelation.Correctors.HeatKernelConvolution

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- AKM's isotropic Gaussian average is a genuine spatial Bochner integral. -/
theorem integrable_isotropicGaussian_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (U : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => (Correctors.euclideanHeatKernel s x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U) := by
  letI := reducedLaw_probability Q
  exact integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    (fun x => (Correctors.euclideanHeatKernel s x : ℂ))
    (Correctors.integrable_euclideanHeatKernel hs).ofReal
    (Complex.continuous_ofReal.comp (Correctors.continuous_euclideanHeatKernel s)) U

end EinsteinFull
