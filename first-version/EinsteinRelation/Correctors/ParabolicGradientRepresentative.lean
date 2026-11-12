import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Integral.Prod

/-! # The actual weak PDE is independent of its gradient representative

Source: `paper/main.tex:789–816,822–840`. Changing the supplied gradient
on a space-time null set preserves its energy class and distributional
parabolic equation, as well as the scalar flow's initial trace.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Source: `paper/main.tex:789–816,822–840`. A space-time representative
change of the actual gradient preserves the full weak parabolic predicate. -/
theorem parabolicSolution_gradient_congr_ae {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G H : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    (hGH : G =ᵐ[volume.restrict (I ×ˢ U)] H) :
    IsParabolicSolution A I U u H := by
  rcases hsol with ⟨hu, hGm, hGlp, hweak, hPDE⟩
  have hGHprod : G =ᵐ[(volume.restrict I).prod (volume.restrict U)] H := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hGH
  refine ⟨hu, hGm.congr hGH, (memLp_congr_ae (hGH.fun_comp euclideanNorm)).mp hGlp, ?_, ?_⟩
  · filter_upwards [hweak, Measure.ae_ae_of_ae_prod hGHprod] with t ht heq
    exact hasWeakGradient_congr_ae hU ht Filter.EventuallyEq.rfl heq
  · intro ψ hψ hψc hψs
    calc
      (∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (H z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) =
          ∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1, 0) +
            dot ((A z.2).mulVec (G z))
              (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
        apply integral_congr_ae
        filter_upwards [hGH] with z hz
        rw [hz]
      _ = 0 := hPDE ψ hψ hψc hψs

/-- Source: `paper/main.tex:789–816`. Retain the same scalar flow,
initial datum and continuity when changing its gradient representative. -/
theorem semigroupSolution_gradient_congr_ae {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G H : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    (hGH : ∀ (a b R : ℝ), 0 < a → a < b → 0 < R →
      G =ᵐ[volume.restrict (Set.Ioo a b ×ˢ originBall d R)] H) :
    IsSemigroupSolution A g u H := by
  refine ⟨hsol.1, ?_, hsol.2.2⟩
  intro a b R ha hab hR
  have hball : IsOpen (originBall d R) := by
    apply isOpen_lt _ continuous_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  exact parabolicSolution_gradient_congr_ae hball
    (hsol.2.1 a b R ha hab hR) (hGH a b R ha hab hR)

/-- Source: `paper/main.tex:789–798`. Almost-everywhere equal initial
fluxes define the same distributional initial datum for the actual flow. -/
theorem semigroupSolution_initialFlux_congr_ae {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g g' : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) (hgg' : g =ᵐ[volume] g') :
    IsSemigroupSolution A g' u G := by
  refine ⟨hsol.1, hsol.2.1, ?_⟩
  intro ψ hψ
  have heq : (∫ x, dot (g x) (gradient ψ x) ∂volume) =
      ∫ x, dot (g' x) (gradient ψ x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hgg'] with x hx
    rw [hx]
  simpa only [heq] using hsol.2.2 ψ hψ

end EinsteinRelation.Correctors
