import EinsteinFull.Frozen.GaussianAverage
import EinsteinRelation.Correctors.HeatSmoothing

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull
open EinsteinRelation

/-- The extended Gaussian averaging seminorm, with AKM spatial scale rho and
isotropic kernel Phi(rho^2,x). The supremum retains infinity. -/
noncomputable def gaussianAveragingSeminorm {d : ℕ} (_hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) : ℝ≥0∞ :=
  ⨆ ρ : ℝ, ⨆ _hρ : 1 ≤ ρ,
    ENNReal.ofReal (ρ ^ ((d : ℝ) / 2) *
      Real.sqrt (∑ j : Fin d,
        ‖∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (F j)‖ ^ 2))

end EinsteinFull
