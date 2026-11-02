import EinsteinFull.Frozen.StationarySchwartzAverage
import EinsteinFull.Calculus.SpatialPairingSupport

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

theorem integrable_stationarySchwartzAverage_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ψ : SchwartzMap (Vec d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => ψ (-x) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) := by
  letI := reducedLaw_probability Q
  apply integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    (fun x => ψ (-x))
  · simpa only [neg_one_smul] using (ψ.integrable.comp_smul (neg_ne_zero.mpr one_ne_zero))
  · exact ψ.continuous.comp continuous_neg

end EinsteinFull
