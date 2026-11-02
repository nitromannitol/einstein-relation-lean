import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Frozen.RegenerationConditionedLaw

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Graph node `app:factorization#coupling-scope`, `paper/main.tex:1474–1487`
(finiteness used at lines 1516–1523). The literal trial construction and full
joint-field records are measurable throughout the factorization root's scope.
Under both actual laws, every fixed cycle occurs at a finite grid time and
its record is the actual shifted path, coins and restricted reduced fields
there. Thus the infinite-time fallback is unused almost surely.
This includes admissible scales below the fixed large construction scale;
no quantitative tail estimate or extra scale threshold is asserted.
Restricted-kernel locality and deterministic slice geometry have their own
graph nodes, with this same coupling and parameter scope. -/
def node_app_u3A_factorization_u23_coupling_u2D_scopeStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∀ k : ℕ,
      Measurable (regenerationTime hd lam l k) ∧
      Measurable (regenerationRecord hd lam l k) ∧
      ∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * k ≤ n ∧
          regenerationTime hd lam l k q.2 =
            (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
          regenerationRecord hd lam l k q =
            Regeneration.futureRecord Δ R q.1 q.2 i ((n : ℝ≥0) * Δ)

end EinsteinFull.Blueprint
