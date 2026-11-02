import EinsteinFull.Frozen.RegenerationCoupling

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Graph node `app:factorization#past-kernel`, `paper/main.tex:1499`.
Every bounded functional of the path through mΔ and coins strictly before m,
vanishing outside paths below v through mΔ, has a quenched expectation with
a joint-field local version in x₁ ≤ v + 3R. The integral uses the actual
coupled kernel, including successful and failed coins; no restricted-kernel
locality premise is assumed. -/
def node_app_u3A_factorization_u23_past_u2D_kernelStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    ∀ (m : ℕ) (v : ℝ) (H : Regeneration.CoupledSample d → ℝ),
      Measurable[Regeneration.finiteHistorySigma Δ m] H →
      Regeneration.BoundedRealTest H →
      (∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ v) → H z = 0) →
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ v + 3 * R}] A ∧
        (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A

end EinsteinFull.Blueprint
