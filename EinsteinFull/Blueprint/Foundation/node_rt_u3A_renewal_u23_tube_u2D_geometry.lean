import EinsteinFull.Frozen.RegenerationCoupling

open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:renewal#tube-geometry`, `paper/main.tex:356–368`.
The two fixed polygonal tubes are independent of the force and path. For
every actual continuous path starting at zero, membership in either rescaled
Euclidean tube forces the first crossing window, admissible rounding, literal
first candidate time and prebridge survival. This is a deterministic path
statement; no probabilistic estimate or successful coin is assumed. -/
def node_rt_u3A_renewal_u23_tube_u2D_geometryStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (l : ℝ), 0 < l →
    let i := Regeneration.Renewal.forceCoord hd
    let γ₂ : ℝ → Vec d := fun u =>
      min ((25 * l / 4) * u) (25 * l / 8) • unitVector i
    let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    ∀ (j : ℕ), j = 2 ∨ j = 3 → ∀ Y : Path d, Y 0 = 0 →
      (∀ u : ℝ≥0, (u : ℝ) ≤ (j : ℝ) - 1 →
        euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal -
          (if j = 2 then γ₂ (u : ℝ) else γ₃ (u : ℝ))) < l / 32) →
      let H := Regeneration.firstHittingAbove Y i (3 * R)
      ENNReal.ofReal (((j : ℝ) - 2 + 1 / 3) / lam ^ 2) < H ∧
      H < ENNReal.ofReal (((j : ℝ) - 2 + 2 / 3) / lam ^ 2) ∧
      Regeneration.IsGoodPassage Δ lam R (3 * lam * R) Y i 0 ∧
      Regeneration.firstRoundedCandidate Δ lam R (3 * lam * R) Y i =
        (((j - 1 : ℕ) : ℝ≥0∞) * (Δ : ℝ≥0∞)) ∧
      (∀ t : ℝ≥0, t ≤ (j - 1 : ℕ) * Δ → -R < Y t i)

end EinsteinFull.Blueprint
