import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinRelation.Regeneration.ForcedBitSlice

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:k-factor`, `paper/main.tex:482–492`.
Choose the cycle count before the observation, time and tests. The whole
finite-tuple kernel (including its conditioned finite-survival version) is
local below the endpoint minus 4R. Factorization includes local Lp tests,
p≥2, and both actual measures; no boundedness premise replaces truncation. -/
def node_rt_u3A_k_u2D_factorStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l δ : ℝ)
    (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ₀ : 0 < δ) (_hδ₁ : δ < 1),
  ∃ C : ℝ, 0 < C ∧
  ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
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
  ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd R) ≠ 0,
  ∀ A : ℝ, l ≤ A →
    let k := max 1 ⌈(A / l + 4) / 10⌉₊
    (k : ℝ) ≤ C * (1 + A) ∧
    (∀ n : ℕ, 2 * k ≤ n → ∀ y : Vec d, ∀ b : Bool,
      ∃ V : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] V ∧
        (fun ω => ∫ z,
          (if z ∈ Γ k n ∧
              y ∈ Regeneration.endpointBall i R (z.1 (((n - 1 : ℕ) : ℝ≥0) * Δ)) ∧
              (b = true → ∀ u : ℝ≥0, u ≤ ((n - 1 : ℕ) : ℝ≥0) * Δ →
                -R < z.1 u i)
            then (1 : ℝ) else 0) ∂K (0, ω)) =ᵐ[Q.measure] V) ∧
    ∀ (p : ℝ), 2 ≤ p → ∀ F : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
      MemLp F (ENNReal.ofReal p) Q.measure →
      ∀ Φ : Regeneration.FutureState d i R → ℝ,
        Measurable Φ → Regeneration.BoundedRealTest Φ → ∀ n : ℕ,
      ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        (∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
            (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F ωz.1 * Φ (regenerationRecord hd lam l k ωz) ∂μ) =
        (∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
        ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
            (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F ωz.1 ∂μ
end EinsteinFull.Blueprint
