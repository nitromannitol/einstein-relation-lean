import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Source: `paper/main.tex:789–816,822–840`. Actual almost-everywhere
changes of parabolic representatives preserve the energy class, spatial
gradient and distributional PDE. -/
theorem parabolicSolution_congr_ae {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {I : Set ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    {u u' : ℝ × Vec d → ℝ} {G G' : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    (hu : u =ᵐ[volume.restrict (I ×ˢ U)] u')
    (hG : G =ᵐ[volume.restrict (I ×ˢ U)] G') :
    IsParabolicSolution A I U u' G' := by
  rcases hsol with ⟨hu_mem, hG_ae, hG_norm, hweak, hPDE⟩
  have hprod_u : u =ᵐ[(volume.restrict I).prod (volume.restrict U)] u' := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hu
  have hprod_G : G =ᵐ[(volume.restrict I).prod (volume.restrict U)] G' := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hG
  refine ⟨(memLp_congr_ae hu).mp hu_mem,
    hG_ae.congr hG,
    (memLp_congr_ae (hG.fun_comp euclideanNorm)).mp hG_norm,
    ?_,
    ?_⟩
  · filter_upwards [hweak, Measure.ae_ae_of_ae_prod hprod_u,
      Measure.ae_ae_of_ae_prod hprod_G] with t ht hu_eq hG_eq
    exact hasWeakGradient_congr_ae hU ht hu_eq hG_eq
  · intro ψ hψ hψc hψs
    calc
      (∫ z in I ×ˢ U, -(u' z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (G' z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) =
          (∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1, 0) +
            dot ((A z.2).mulVec (G z))
              (fun j => fderiv ℝ ψ z (0, unitVector j))) := by
        apply integral_congr_ae
        filter_upwards [hu, hG] with z huz hGz
        simp [huz, hGz]
      _ = 0 := hPDE ψ hψ hψc hψs

end EinsteinRelation.Correctors
