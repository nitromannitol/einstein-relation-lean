import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.CorrectorGradient
import EinsteinFull.Frozen.HomogenizedGaussianKernel

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `corrector-construction#smooth-moments`, `paper/main.tex:794`,
used at lines 880–885. Every finite moment is bounded for the canonical real
gradient and the positive-Gaussian weighted gradient normalization of
`x_i + phi_i`. The Gaussian uses the actual anisotropic homogenized matrix
and time `r^2`; changing this fixed normalization is harmless in the source.
The moment constant is selected before the law, coordinate, point and scale.
No stationary scalar potential is requested. -/
def node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p : ℝ), 1 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (z : Vec d),
      MemLp (fun ω => correctorGradient Q i (translate z ω))
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∫ ω, ‖correctorGradient Q i (translate z ω)‖ ^ p ∂reducedLaw Q) ≤ C ∧
      ∀ (r : ℝ) (hr : 1 ≤ r),
        (∀ᵐ ω ∂reducedLaw Q,
          Integrable (fun x : Vec d =>
            (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
              (by positivity) 0 (z - x)).re *
            euclideanSq (unitVector i +
              WithLp.ofLp (correctorGradient Q i (translate x ω))))) ∧
        MemLp (fun ω => Real.sqrt (∫ x : Vec d,
          (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
            (by positivity) 0 (z - x)).re *
          euclideanSq (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x ω)))))
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (∫ ω, (Real.sqrt (∫ x : Vec d,
          (homogenizedGaussianKernel Q ⟨0, by omega⟩ (r ^ 2)
            (by positivity) 0 (z - x)).re *
          euclideanSq (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x ω))))) ^ p
          ∂reducedLaw Q) ≤ C

end EinsteinFull.Blueprint
