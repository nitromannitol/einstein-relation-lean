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

/-- Graph node `e:linear-velocity#spectral-integral`, `paper/main.tex:1285–1290`.
The integral is of the actual unforced correlation and its energy uses the
same law and canonical gradients. Integrability is a conclusion. -/
def node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integralStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      let first : Fin d := ⟨0, by omega⟩
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q first 0 P → ∀ i : Fin d,
        IntegrableOn (fun t : ℝ =>
          (velocityCorrelation Q first i 0 P β a t.toNNReal).re) (Set.Ici 0) ∧
        (∫ t in Set.Ici (0 : ℝ),
          (velocityCorrelation Q first i 0 P β a t.toNNReal).re) =
          (1 / 2 : ℝ) * (∫ ω, ∑ j : Fin d, ∑ k : Fin d,
          (correctorGradient Q first ω j) * ω.1 0 j k *
            (correctorGradient Q i ω k) ∂reducedLaw Q)

end EinsteinFull.Blueprint
