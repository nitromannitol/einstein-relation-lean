import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinRelation.Regeneration.ForcedBitSlice

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:global-geometry`, `paper/main.tex:473–480`.
Literal prebridge maxima and Euclidean endpoint balls, with the source constants
10 and 7. The actual coupling supplies earlier successful-bridge geometry;
the endpoint is universally quantified in the final ball. The bridge bound
11R is used by the source induction, not assumed as an extra premise. -/
def node_rt_u3A_global_u2D_geometryStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ₀ : 0 < δ) (_hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let tupleEvent := fun (k n : ℕ) (a : Fin (k + 1) → ℕ) =>
    {z : Regeneration.CoupledSample d |
      a 0 = 0 ∧ a (Fin.last k) = n ∧
      (∀ j : Fin k, a j.castSucc + 2 ≤ a j.succ) ∧
      (∀ j : Fin k,
        Regeneration.sampleTimeShift Δ z ((a j.castSucc : ℝ≥0) * Δ) ∈
          Regeneration.forcedBitTrialEvent Δ lam R i (a j.succ - a j.castSucc - 1)) ∧
      (∀ j : Fin k, j.val + 1 < k → z.2 (a j.succ - 1) = true) ∧
      (∀ j : Fin k, j.val + 1 < k → ∀ u : ℝ≥0,
        (a j.succ : ℝ≥0) * Δ ≤ u → u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
        z.1 ((a j.succ : ℝ≥0) * Δ) i - R < z.1 u i)}
  let Γ := fun k n => ⋃ a : Fin (k + 1) → Fin (n + 1),
    tupleEvent k n (fun j => (a j).val)
  ∀ᵐ ωz ∂Regeneration.annealedCoupledLaw Q.measure K,
    ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n → ωz.2 ∈ Γ k n →
      let z := ωz.2.1 (((n - 1 : ℕ) : ℝ≥0) * Δ)
      (∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ → ωz.2.1 u i ≤ z i + R) ∧
      ∀ y ∈ Regeneration.endpointBall i R z,
        10 * (k : ℝ) * R ≤ y i ∧
        ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ → ωz.2.1 u i ≤ y i - 7 * R
end EinsteinFull.Blueprint
