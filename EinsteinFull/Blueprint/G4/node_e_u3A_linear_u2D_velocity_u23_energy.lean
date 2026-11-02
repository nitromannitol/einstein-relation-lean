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

/-- Graph node `e:linear-velocity#energy`, `paper/main.tex:1290–1295`.
The canonical potential gradients are used directly, including in dimension
two. No scalar stationary corrector or corrector identity is assumed. -/
def node_e_u3A_linear_u2D_velocity_u23_energyStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    let first : Fin d := ⟨0, by omega⟩
    ∀ i : Fin d,
      homogenizedCoefficient Q first i =
        (∫ ω, ω.1 0 first i ∂reducedLaw Q) -
        (∫ ω, ∑ j : Fin d, ∑ k : Fin d,
          (correctorGradient Q first ω j) * ω.1 0 j k *
            (correctorGradient Q i ω k) ∂reducedLaw Q)

end EinsteinFull.Blueprint
