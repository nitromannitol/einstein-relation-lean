import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedLaw

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `l:forced-local#cutoff-environment`, `paper/main.tex:669–670`.
A deterministic smooth annular cutoff retains the actual reduced pair in the
Euclidean ball of radius ρ and replaces it by `(Id, 1)` outside radius 2ρ.
The explicit convex interpolation retains anisotropic ellipticity and bounds
all positive derivative orders uniformly over the centers, the unit-or-larger
radii used in the localization estimates, and the law. The cutoff is chosen
before the law; the same almost-sure event covers every center and radius.
Sources built locally from the pair and its derivatives therefore agree on
the retained open ball. No stochastic law for the modified pair is asserted. -/
def node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt : Prop :=
  ∀ (d : ℕ) (D : StructuralData d),
    ∃ Λ : ℝ, ∃ M K : ℕ → ℝ,
      1 ≤ Λ ∧ (∀ k : ℕ, 1 ≤ k → 0 < M k ∧ 0 < K k) ∧
    ∃ χ : Vec d → ℝ → Vec d → ℝ,
      (∀ (z : Vec d) (ρ : ℝ), 1 ≤ ρ →
        ContDiff ℝ (⊤ : ℕ∞) (χ z ρ) ∧
        (∀ x, 0 ≤ χ z ρ x ∧ χ z ρ x ≤ 1) ∧
        (∀ x, euclideanNorm (x - z) ≤ ρ → χ z ρ x = 1) ∧
        (∀ x, 2 * ρ ≤ euclideanNorm (x - z) → χ z ρ x = 0) ∧
        ∀ k : ℕ, 1 ≤ k → ∀ (x : Vec d) (v : Fin k → Vec d),
          |iteratedFDeriv ℝ k (χ z ρ) x v| ≤
            K k * ρ ^ (-(k : ℤ)) * ∏ j, euclideanNorm (v j)) ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
          ∀ (z : Vec d) (ρ : ℝ), 1 ≤ ρ → ∃ ωloc : FieldPair d,
            (∀ x, ωloc.1 x =
              χ z ρ x • ω.1 x + (1 - χ z ρ x) • (1 : Mat d)) ∧
            (∀ x, ωloc.2 x = χ z ρ x * ω.2 x + (1 - χ z ρ x)) ∧
            (∀ x, euclideanNorm (x - z) ≤ ρ →
              ωloc.1 x = ω.1 x ∧ ωloc.2 x = ω.2 x) ∧
            (∀ x, 2 * ρ ≤ euclideanNorm (x - z) →
              ωloc.1 x = (1 : Mat d) ∧ ωloc.2 x = 1) ∧
            IsElliptic Λ ωloc.1 ∧
            (∀ x, Λ⁻¹ ≤ ωloc.2 x ∧ ωloc.2 x ≤ Λ) ∧
            IsSmoothWithBounds M ωloc

end EinsteinFull.Blueprint
