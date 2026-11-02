import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedLaw

open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `l:forced-local#point-kernel`, `paper/main.tex:713`.
For the actual smooth reduced coefficients, the physical forward evolution
and its bilinear transpose admit a spatial integral kernel. At times at least
two its continuous first spatial derivatives have Gaussian off-diagonal bounds
with a structural polynomial prefactor. Both spatial variables are controlled;
the transpose uses the spatially swapped kernel, without conjugation.
Integrating against bounded data gives an actual differentiable spatial
function, with the same polynomial growth bound for its Euclidean gradient.
Constants precede the law, and one environment event precedes forces and data.
No physical kernel or regularity estimate is a premise. -/
def node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ D : StructuralData d,
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
      IsPhysicalComplexKernel P Pdag K ∧
      ∀ H ∈ [K, fun t x y => K t y x],
      ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) →
        ContDiff ℝ 1 (fun z : Vec d × Vec d => H t z.1 z.2) ∧
        (∀ x y : Vec d,
          ‖H t x y‖ +
            Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ (fun z => H t z y) x (unitVector j)‖ ^ 2) +
            Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ (fun z => H t x z) y (unitVector j)‖ ^ 2) ≤
          C * (2 + (t : ℝ)) ^ N *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) -
              c * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
        (∀ (f : Vec d → ℂ) (B : ℝ), 0 ≤ B →
          AEStronglyMeasurable f volume → (∀ᵐ y ∂volume, ‖f y‖ ≤ B) →
          let u := fun x => ∫ y, H t x y * f y
          Differentiable ℝ u ∧ ∀ x : Vec d,
            Integrable (fun y => H t x y * f y) ∧
            (∀ j : Fin d,
              Integrable (fun y =>
                fderiv ℝ (fun z => H t z y) x (unitVector j) * f y) ∧
              fderiv ℝ u x (unitVector j) =
                ∫ y, fderiv ℝ (fun z => H t z y) x (unitVector j) * f y) ∧
            ‖u x‖ + Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
              C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B)

end EinsteinFull.Blueprint
