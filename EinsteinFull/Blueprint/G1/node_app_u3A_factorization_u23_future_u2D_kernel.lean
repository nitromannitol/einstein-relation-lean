import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationConditionedLaw
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Graph node `app:factorization#future-kernel`, `paper/main.tex:1501`.
Every bounded measurable observable of the complete path/coin/restricted-joint-field
triple, killed on D at the origin, has a future-half-space measurable version.
The record contains both reduced a and mu; no locality premise is inserted. -/
def node_app_u3A_factorization_u23_future_u2D_kernelStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∀ (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∃ B : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          -2 * (l / lam) ≤ x (Regeneration.Renewal.forceCoord hd)}] B ∧
        (fun ω => ∫ z, Regeneration.killedFutureTest (l / lam)
          (Regeneration.Renewal.forceCoord hd) Φ ((0, ω), z) ∂K (0, ω)) =ᵐ[Q.measure] B

end EinsteinFull.Blueprint
