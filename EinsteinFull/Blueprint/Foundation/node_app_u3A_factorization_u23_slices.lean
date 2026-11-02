import EinsteinFull.Frozen.RegenerationTime
import EinsteinRelation.Regeneration.ForcedBitSlice

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Graph node `app:factorization#slices`, `paper/main.tex:1490–1497`
(also `315–327`). The literal forced-last-bit trial event is measurable
before the final coin and decomposes the actual first regeneration slice.
On paths starting at the origin its selected prebridge position and every
endpoint in the Euclidean bridge ball satisfy the source bounds 2R, 10R
and 7R. No stopping-time assertion at the regeneration time is made. -/
def node_app_u3A_factorization_u23_slicesStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    ∀ (n : ℕ), 2 ≤ n →
    let T := ((n - 1 : ℕ) : ℝ≥0) * Δ
    let Γ := Regeneration.forcedBitTrialEvent Δ lam R i (n - 1)
    MeasurableSet[Regeneration.finiteHistorySigma Δ (n - 1)] Γ ∧
      (∀ z : Regeneration.CoupledSample d,
        regenerationTime hd lam l 1 z = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔
          z ∈ Γ ∧ z.2 (n - 1) = true ∧
            Regeneration.NoBacktracking R
              (Regeneration.pathTimeShift z.1 ((n : ℝ≥0) * Δ)) i) ∧
      (∀ z : Regeneration.CoupledSample d, z.1 0 = 0 → z ∈ Γ →
        let a := z.1 T
        2 * R ≤ a i ∧
          (∀ t : ℝ≥0, t ≤ T → z.1 t i ≤ a i + R) ∧
          ∀ y : Vec d, y ∈ Regeneration.endpointBall i R a →
            10 * R ≤ y i ∧
              ∀ t : ℝ≥0, t ≤ T → z.1 t i ≤ y i - 7 * R)

end EinsteinFull.Blueprint
