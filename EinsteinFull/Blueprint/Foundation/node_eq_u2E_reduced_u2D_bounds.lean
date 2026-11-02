import EinsteinFull.Frozen.ReducedLaw

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `eq.reduced-bounds`, `paper/main.tex:216–221`.
The structural bound and both Lipschitz constants precede the law. The law
and its restrictions are those of the actual joint reduced pair `(a, μ)`. -/
def node_eq_u2E_reduced_u2D_boundsStmt : Prop :=
  ∀ Λ₀ : ℝ, 1 ≤ Λ₀ → ∃ Λ A B : ℝ,
    1 ≤ Λ ∧ 0 ≤ A ∧ 0 ≤ B ∧ A + B ≤ Λ ∧
    ∀ (d : ℕ) (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
      IsStationary (reducedLaw Q) ∧ HasFiniteRange r₀ (reducedLaw Q) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        IsElliptic Λ ω.1 ∧ (∀ x, Λ⁻¹ ≤ ω.2 x ∧ ω.2 x ≤ Λ) ∧
        IsOperatorLipschitz A ω.1 ∧
        ∀ x y, |ω.2 x - ω.2 y| ≤ B * euclideanNorm (x - y)

end EinsteinFull.Blueprint
