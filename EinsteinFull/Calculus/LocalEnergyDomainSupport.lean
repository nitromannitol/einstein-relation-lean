import EinsteinFull.Frozen.LocalSpatialEnergy
import EinsteinRelation.Correctors.SpatialBallVolume

open scoped NNReal
open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- Positive-radius Euclidean windows have positive finite coordinate volume.
The proof generalizes the blueprint's `Correctors.ball_volume_pos_finite`
from the origin to an arbitrary centre, retaining the Euclidean norm. -/
theorem localSpatialEnergy_window_volume {d : ℕ} (x : Vec d) (ρ : ℝ) (hρ : 0 < ρ) :
    0 < volume.real {y : Vec d | euclideanNorm (y - x) < ρ} := by
  have hU : IsOpen {y : Vec d | euclideanNorm (y - x) < ρ} := by
    unfold euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hne : {y : Vec d | euclideanNorm (y - x) < ρ}.Nonempty := by
    refine ⟨x, ?_⟩
    simp [euclideanNorm, euclideanSq, dot, hρ]
  have hfin : volume {y : Vec d | euclideanNorm (y - x) < ρ} ≠ ⊤ := by
    have hsub : {y : Vec d | euclideanNorm (y - x) < ρ} ⊆ Metric.closedBall x ρ := by
      intro y hy
      rw [Metric.mem_closedBall, dist_pi_le_iff hρ.le]
      intro j
      rw [Real.dist_eq]
      exact (Regeneration.coordinate_abs_le_euclideanNorm (y - x) j).trans hy.le
    have hclosed : volume (Metric.closedBall x ρ) ≠ ⊤ := by
      rw [Real.volume_pi_closedBall _ hρ.le]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hclosed (measure_mono hsub)
  exact ENNReal.toReal_pos (hU.measure_pos volume hne).ne' hfin

/-- The square of the local energy is its actual normalized spatial integral. -/
theorem localSpatialEnergy_sq {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    (ω : FieldPair d) :
    localSpatialEnergy Q t ρ hρ x G V ω ^ 2 =
      ⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ},
        (∑ j : Fin d, ‖G j (translate y ω)‖ ^ 2) + (t : ℝ) * ‖V (translate y ω)‖ ^ 2 := by
  apply Real.sq_sqrt
  apply integral_nonneg
  intro y
  exact add_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)
    (mul_nonneg t.property (sq_nonneg _))

end EinsteinFull
