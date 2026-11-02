import EinsteinRelation.External.GilbargTrudinger
import EinsteinRelation.Calculus.SpatialL2Convergence
import EinsteinRelation.TimeChange.EuclideanTransport

/-!
# Poincaré for centered scalar L² classes

Source: `paper/main.tex:722-729`. This is the existing explicit GT ball
Poincaré proposition expressed in the actual Hilbert norms used for limits.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Centered scalar classes are controlled by their Euclidean weak gradients. -/
theorem centered_L2_poincare (hP : BallPoincareEstimate) (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : Vec d) (R : ℝ), 0 < R →
      ∀ (u : Lp ℝ 2 (volume.restrict (ball y R)))
        (g : Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict (ball y R))),
        HasWeakGradient (ball y R) u (fun x => (g x).ofLp) →
        (⨍ x in ball y R, u x ∂volume) = 0 → ‖u‖ ≤ C * R * ‖g‖ := by
  obtain ⟨C, hC, hest⟩ := hP d hd
  refine ⟨C, hC, fun y R hR u g hweak hmean => ?_⟩
  have hg : MemLp (fun x => (g x).ofLp) 2 (volume.restrict (ball y R)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.comp_memLp g
  have h := hest y R hR u (fun x => (g x).ofLp) (Lp.memLp u) hg hweak
  have hu := norm_toLp_eq_sqrt_integral_norm_sq
    (volume.restrict (ball y R)) u (Lp.memLp u)
  have hgn := norm_toLp_eq_sqrt_integral_norm_sq
    (volume.restrict (ball y R)) g (Lp.memLp g)
  rw [Lp.toLp_coeFn] at hu hgn
  rw [hu, hgn]
  convert h using 2
  · simp only [hmean, sub_zero, Real.norm_eq_abs]
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [EuclideanSpace.norm_sq_eq]
    simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]

end EinsteinRelation.Correctors
