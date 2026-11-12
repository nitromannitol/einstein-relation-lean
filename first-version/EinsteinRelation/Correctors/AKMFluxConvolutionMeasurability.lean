import EinsteinRelation.Correctors.AKMSourceMeasurableEnergy
import EinsteinRelation.Correctors.MollifierShiftSourceIdentity

/-! # Measurability of literal source flux convolutions

Source: `paper/main.tex:948–955`. The raw coefficient evaluation is replaced
only inside a spatial integral by its jointly measurable representative,
which agrees spatially almost everywhere for every coefficient separately.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The centered literal flux convolution is jointly measurable in its
center and raw coefficient, without a pointwise measurable evaluation of the
raw coefficient. Source: `paper/main.tex:948–955`. -/
theorem measurable_rawFlux_convolution_joint {d : ℕ} {K : ℝ}
    (G : Coefficient d K → Vec d → Vec d)
    (hG : Measurable (Function.uncurry G)) (e q : Vec d) (j : Fin d)
    {ζ : Vec d → ℝ} (hζ : Continuous ζ) :
    Measurable (fun z : Vec d × Coefficient d K =>
      ((fun x => ((z.2 x).mulVec (e + G z.2 x) - q) j)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) z.1) := by
  have hm : Measurable (fun p : Coefficient d K × Vec d =>
      (sourceFluxRepresentative G e p.1 p.2 - q) j) :=
    (measurable_pi_apply j).comp
      ((measurable_sourceFluxRepresentative G hG e).sub measurable_const)
  have heq : (fun z : Vec d × Coefficient d K =>
      ((fun x => (sourceFluxRepresentative G e z.2 x - q) j)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) z.1) =
      (fun z : Vec d × Coefficient d K =>
      ((fun x => ((z.2 x).mulVec (e + G z.2 x) - q) j)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ζ) z.1) := by
    funext z
    apply integral_congr_ae
    filter_upwards [sourceFluxRepresentative_ae_eq G e z.2] with x hx
    change (sourceFluxRepresentative G e z.2 x - q) j * ζ (z.1 - x) = _
    rw [hx]
    rfl
  rw [← heq]
  exact measurable_random_convolution_joint
    (fun A x => (sourceFluxRepresentative G e A x - q) j) hm hζ

end EinsteinRelation.Correctors
