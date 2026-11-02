import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationConditionedLaw
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Graph node `app:factorization#endpoint-disintegration`,
`paper/main.tex:1503–1515`. Literal deterministic prebridge disintegration for
product future observables, including H, all spatial endpoints, and the exact
successful-coin probability divided by the Euclidean endpoint-ball volume. -/
def node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    ∀ (F : FieldPair d → ℝ),
      Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
      Regeneration.BoundedRealTest F →
    ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
      Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
      Regeneration.BoundedRealTest H →
    ∀ (f : Path d × Regeneration.BernoulliSequence → ℝ),
      Measurable f → Regeneration.BoundedRealTest f →
    ∀ (g : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) → ℝ),
      Measurable g → Regeneration.BoundedRealTest g →
    let Φ := fun r : Regeneration.FutureState d i R => f (r.1, r.2.1) * g r.2.2
    let A := fun (y : Vec d) (ω : FieldPair d) =>
      F ω * Regeneration.firstSlicePastIntegral Δ lam R i (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      (δ / (volume (Regeneration.endpointBall i R (0 : Vec d))).toReal) *
        ∫ y, ∫ ω, A y ω * B y ω ∂Q.measure

end EinsteinFull.Blueprint
