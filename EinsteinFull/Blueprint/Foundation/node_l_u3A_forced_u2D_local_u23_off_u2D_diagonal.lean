import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Frozen.ReducedLaw

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `l:forced-local#off-diagonal`, `paper/main.tex:707–713`.
The physical forward evolution and its true bilinear transpose satisfy the
exponential-weight estimate on the genuine multiplication domain and the
Gaussian estimate between separated spatial sets. Constants precede the law
and a single full-measure event precedes all forces, evolutions and tests.
No coefficient derivatives are needed for this energy step. In particular,
the exponential multipliers are not asserted to act boundedly on all L2. -/
def node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ₀ : ℝ, 1 ≤ Λ₀ → ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀), ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ (t : ℝ≥0), 0 < t →
      (∀ (q : ℝ) (ψ : Vec d → ℝ),
        (∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y)) →
        ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
          MemLp (fun x => (Real.exp (q * ψ x) : ℂ) * f x) 2 volume →
          MemLp (fun x => (Real.exp (q * ψ x) : ℂ) * S t f x) 2 volume ∧
          (eLpNorm (fun x => (Real.exp (q * ψ x) : ℂ) * S t f x) 2 volume).toReal ≤
            Real.exp (C * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ)) *
              (eLpNorm (fun x => (Real.exp (q * ψ x) : ℂ) * f x) 2 volume).toReal) ∧
      (∀ (E F : Set (Vec d)), MeasurableSet E → MeasurableSet F →
        ∀ ℓ : ℝ, 0 ≤ ℓ → (∀ x ∈ E, ∀ y ∈ F, ℓ ≤ euclideanNorm (x - y)) →
        ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
          (∀ᵐ x ∂volume, x ∉ E → f x = 0) →
          MemLp (F.indicator (fun x => S t f x)) 2 volume ∧
          (eLpNorm (F.indicator (fun x => S t f x)) 2 volume).toReal ≤
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ℓ ^ 2 / (t : ℝ)) * ‖f‖)

end EinsteinFull.Blueprint
