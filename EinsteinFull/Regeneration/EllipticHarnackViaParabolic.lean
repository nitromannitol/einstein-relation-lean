import EinsteinFull.Regeneration.StationaryHarnack
import EinsteinFull.Regeneration.StationaryEllipticLift

/-!
# Elliptic Harnack comparison through stationary parabolic solutions

Parabolic Harnack yields pointwise comparison of continuous elliptic `L²`
weak solutions in every positive dimension.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A continuous elliptic `L²` weak solution satisfies pointwise Harnack comparison. -/
theorem elliptic_pointwise_harnack_of_parabolic_coeff (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (a : PDE.CoeffField d) (τ θ : ℝ), 0 < θ →
      ∀ z z' : PDE.Vec d, PDE.euclideanSqDist z z' ≤ θ / 4 →
      PDE.IsParabolicCoeff 1 Λ (fun p => a p.1)
        (PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) →
      ∀ u : PDE.H1Function
        (PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ))),
      PDE.IsWeakDivergenceFormL2SolutionOn a _ u 0 0 →
      Continuous u.toFun → (∀ x, 0 ≤ u.toFun x) → u z ≤ H * u z' := by
  obtain ⟨H, hH, hcomp⟩ := stationary_pointwise_harnack d hd Λ hΛ
  refine ⟨H, hH, ?_⟩
  intro a τ θ hθ z z' hdist hcoeff u hsol hcont hnonneg
  let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ))
  let I := Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)
  let : IsFiniteMeasure (volume.restrict I : Measure ℝ) := by dsimp [I]; infer_instance
  let w := stationaryParH1 U I u.toFun u.grad u.memL2 u.gradMemL2 u.hasWeakGradient
  have hw : PDE.IsParabolicWeakSolution (fun p => a p.1) U I w :=
    elliptic_l2_solution_stationary (PDE.isOpen_euclideanBall _ _) I a u hsol
  exact hcomp (fun p => a p.1) τ θ hθ z z' hdist hcoeff w hw u.toFun hcont hnonneg
    (fun _ _ => rfl)

end EinsteinFull.Regeneration
