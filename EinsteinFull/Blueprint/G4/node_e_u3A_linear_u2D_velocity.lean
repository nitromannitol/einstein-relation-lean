import EinsteinFull.Blueprint.Roots.node_p_u3A_profile
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient
import EinsteinFull.Frozen.CriticalKernelTerm
import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Frozen.ReducedClockRate

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:linear-velocity`, `paper/main.tex:1279–1298`.
The spectral identity and the tested corrector energy identify every
component of the actual linear velocity coefficient with the averaged flux. -/
def node_e_u3A_linear_u2D_velocityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      let first : Fin d := ⟨0, by omega⟩
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q first 0 P → ∀ i : Fin d,
        (IntegrableOn (fun t : ℝ =>
          (velocityCorrelation Q first i 0 P β a t.toNNReal).re) (Set.Ici 0) ∧
        (∫ t in Set.Ici (0 : ℝ),
          (velocityCorrelation Q first i 0 P β a t.toNNReal).re) =
          (1 / 2 : ℝ) * (∫ ω, ∑ j : Fin d, ∑ k : Fin d,
          (correctorGradient Q first ω j) * ω.1 0 j k *
            (correctorGradient Q i ω k) ∂reducedLaw Q)) ∧
        (∫ ω, ω.1 0 first i ∂reducedLaw Q) -
          2 * (∫ t in Set.Ici (0 : ℝ),
            (velocityCorrelation Q first i 0 P β a t.toNNReal).re) =
          homogenizedCoefficient Q first i

end EinsteinFull.Blueprint
