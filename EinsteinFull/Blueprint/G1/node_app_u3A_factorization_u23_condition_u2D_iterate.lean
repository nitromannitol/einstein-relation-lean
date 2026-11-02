import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationConditionedLaw
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Graph node `app:factorization#condition-iterate`, `paper/main.tex:1518–1523`.
Initial no-return on a selected slice is the literal prebridge survival event.
A measurable shift of the actual restricted triple preserves its conditioned
law and composes the actual records. All cycle marginals and deterministic
slice factorizations hold under both annealed and D-conditioned laws.
The statement does not assert that a regeneration time is a stopping time. -/
def node_app_u3A_factorization_u23_condition_u2D_iterateStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0,
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    (∀ n : ℕ, 2 ≤ n → ∀ᵐ q ∂μ,
      regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd R ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Δ → -R < q.2.1 s i)) ∧
    (∃ Θ : Regeneration.FutureState d i R → Regeneration.FutureState d i R,
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν) ∧
    (∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ q, Φ (regenerationRecord hd lam l k q) ∂ρ) =
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
        (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂ρ) *
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν))

end EinsteinFull.Blueprint
