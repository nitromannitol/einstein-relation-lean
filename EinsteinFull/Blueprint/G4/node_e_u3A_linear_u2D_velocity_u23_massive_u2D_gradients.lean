import EinsteinFull.Blueprint.Roots.node_p_u3A_profile
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient
import EinsteinFull.Frozen.CriticalKernelTerm
import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Calculus.ComplexGeneratorOperatorSupport
import EinsteinFull.Frozen.ReducedClockRate

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:linear-velocity#massive-gradients`, `paper/main.tex:1285–1290`.
The positive mass tends to zero on its actual domain. Only gradients of
the actual full-generator resolvents converge; no scalar limit is asserted. -/
def node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradientsStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
      let first : Fin d := ⟨0, by omega⟩
      ∀ i : Fin d,
      ∃ G : Set.Ioi (0 : ℝ) → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ s : Set.Ioi (0 : ℝ),
          HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
            (unforcedComplexResolvent Q first s.val s.property (β i)) (G s)) ∧
        Tendsto (fun s : Set.Ioi (0 : ℝ) => ∫ ω,
          ∑ j : Fin d, ∑ k : Fin d, ω.1 0 j k *
            (((G s j ω).re - correctorGradient Q i ω j) *
              ((G s k ω).re - correctorGradient Q i ω k) +
              (G s j ω).im * (G s k ω).im) ∂reducedLaw Q)
          (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0)

end EinsteinFull.Blueprint
