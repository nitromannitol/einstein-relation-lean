import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinRelation.Regeneration.ForcedBitSlice

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:prebridge-k`, `paper/main.tex:455–471`.
The finite union enumerates bounded integer tuples, with literal translated
forced-last-bit trials and finite survival checks. The slice and unique tuple
claims hold almost surely for the actual coupling; bridge support is a law
property, not a condition imposed on arbitrary continuous paths. The history
measurability assertion itself is deterministic. No stopping-time assertion
about a regeneration time is made. -/
def node_rt_u3A_prebridge_u2D_kStmt : Prop :=
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
  ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n →
    @MeasurableSet (Regeneration.CoupledSample d)
      (Regeneration.finiteHistorySigma Δ (n - 1)) (Γ k n) ∧
    (∀ᵐ ωz ∂Regeneration.annealedCoupledLaw Q.measure K,
      (regenerationTime hd lam l k ωz.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔
        ωz.2 ∈ Γ k n ∧ ωz.2.2 (n - 1) = true ∧
          Regeneration.NoBacktracking R
            (Regeneration.pathTimeShift ωz.2.1 ((n : ℝ≥0) * Δ)) i) ∧
      (ωz.2 ∈ Γ k n → ωz.2.2 (n - 1) = true →
        Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift ωz.2.1 ((n : ℝ≥0) * Δ)) i →
        ∃! a : Fin (k + 1) → Fin (n + 1),
          ωz.2 ∈ tupleEvent k n (fun j => (a j).val) ∧
          ∀ j : Fin (k + 1), regenerationTime hd lam l j.val ωz.2 =
            ((((a j).val : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)))
end EinsteinFull.Blueprint
