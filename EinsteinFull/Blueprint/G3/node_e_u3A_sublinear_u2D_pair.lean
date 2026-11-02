import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.CorrectorGradient
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinRelation.Environment.MatrixNorm
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:sublinear-pair`, `paper/main.tex:801–807`.
Scalar and antisymmetric flux potentials are constructed for the actual
canonical gradient and expected flux, with the column-divergence convention.
Only gradients are stationary. On each good event constants may depend on
the environment, scale and center. Both spatial norms are volume-normalized
Euclidean/Frobenius L2 norms on the same ball. -/
def node_e_u3A_sublinear_u2D_pairStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (D : StructuralData d),
    ∃ κ C c : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
      ∃ (φ : Fin d → FieldPair d → Vec d → ℝ)
        (S : Fin d → FieldPair d → Vec d → Mat d),
        (∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
          ContDiff ℝ (⊤ : ℕ∞) (φ i ω) ∧
          (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => S i ω x j k)) ∧
          (∀ x, (S i ω x).transpose = -(S i ω x)) ∧
          ∀ᵐ x ∂(volume : Measure (Vec d)),
            (∀ j : Fin d, fderiv ℝ (φ i ω) x (unitVector j) =
              correctorGradient Q i (translate x ω) j) ∧
            ∀ j : Fin d,
              (∑ k : Fin d, fderiv ℝ (fun y => S i ω y k j) x (unitVector k)) =
                ((ω.1 x).mulVec (unitVector i +
                  WithLp.ofLp (correctorGradient Q i (translate x ω)))) j -
                    homogenizedCoefficient Q j i) ∧
        ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
          ∃ E : Set (FieldPair d), MeasurableSet E ∧
            reducedLaw Q Eᶜ ≤ ENNReal.ofReal
              (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
            ∀ ω ∈ E, ∃ (a : Fin d → ℝ) (b : Fin d → Mat d),
              let B := {x : Vec d | euclideanNorm (x - z) < C * r}
              (∑ i : Fin d, (
                Real.sqrt ((volume B).toReal⁻¹ *
                  ∫ x in B, |φ i ω x - a i| ^ 2) +
                Real.sqrt ((volume B).toReal⁻¹ *
                  ∫ x in B, frobeniusNorm (S i ω x - b i) ^ 2))) ≤
                    C * r ^ (1 - κ)

end EinsteinFull.Blueprint
