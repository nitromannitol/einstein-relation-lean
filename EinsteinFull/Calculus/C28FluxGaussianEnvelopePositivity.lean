import EinsteinFull.Calculus.CarverSFluxBlockGain

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The Gaussian spatial envelope is positive on every nonempty closed ball. -/
theorem c28_actual_gaussian_spatial_envelope_positive
    {d : ℕ} (s Cenv : ℝ) (hs : 0 < s) (x z : Vec d) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let w := fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))
    0 < sSup (w '' {y : Vec d | euclideanNorm (y - z) ≤ ρ}) := by
  intro w
  have hz : z ∈ {y : Vec d | euclideanNorm (y - z) ≤ ρ} := by
    simpa [euclideanNorm, euclideanSq, dot] using hρ
  have hpoint : 0 < w z := by
    dsimp [w]
    exact mul_pos (Real.rpow_pos_of_pos hs _) (Real.exp_pos _)
  have hbound := (carverS_flux_block_gaussian_spatial_sup s hs Cenv x z ρ hρ).2.2 z hz
  exact lt_of_lt_of_le hpoint hbound

end EinsteinFull.Blueprint
