import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup

import EinsteinFull.Frozen.IndexedEndpoint
import EinsteinFull.Frozen.LocalSpatialEnergy
import EinsteinFull.Frozen.ComplexHorizontalGradient

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `e:energy-target`, `paper/main.tex:777–784`.
The literal normalized local Euclidean gradient energy, integrated on [t,2t]
and summed over velocity and transpose endpoints. The clock is absent from
this displayed energy target. The actual horizontal gradients are produced,
not assumed. Scalar decay and the centered energy inequality are proof steps. -/
def node_e_u3A_energy_u2D_targetStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∃ (G : EndpointIndex d → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
      (g : EndpointIndex d → ℝ × FieldPair d → Fin d → ℂ),
      (∀ (ν : EndpointIndex d), ν ≠ Sum.inr false →
        ∀ j : Fin d, AEStronglyMeasurable (fun z => g ν z j)
          (volume.prod (reducedLaw Q))) ∧
      (∀ (ν : EndpointIndex d), ν ≠ Sum.inr false →
        ∀ r : ℝ≥0, 0 < (r : ℝ) → ∀ j : Fin d,
          (fun ω => g ν ((r : ℝ), ω) j) =ᵐ[reducedLaw Q]
            (G ν r j : FieldPair d → ℂ)) ∧
      (∀ (ν : EndpointIndex d), ν ≠ Sum.inr false →
        ∀ r : ℝ≥0, 0 < (r : ℝ) →
          HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
            (indexedEndpoint hd Q ν ζ P Pdag β a μ r) (G ν r)) ∧
      ∀ t : ℝ, 1 ≤ t → ‖ζ‖ * Real.sqrt (2 * t) ≤ 2 →
        let E := fun (ν : EndpointIndex d) (ω : FieldPair d) =>
          Real.sqrt (∫ r in Set.Icc t (2 * t),
            ⨍ y in {y : Vec d | euclideanNorm y < 1},
              ∑ j : Fin d, ‖g ν (r, translate y ω) j‖ ^ 2)
        (∀ ν : EndpointIndex d, ν ≠ Sum.inr false →
          IntegrableOn (fun r : ℝ =>
            ∫ ω, ∑ j : Fin d, ‖g ν (r, ω) j‖ ^ 2 ∂reducedLaw Q)
            (Set.Icc t (2 * t)) ∧ MemLp (E ν) 2 (reducedLaw Q)) ∧
        (eLpNorm (E (Sum.inr true)) 2 (reducedLaw Q)).toReal +
          (∑ i : Fin d, (eLpNorm (E (Sum.inl i)) 2 (reducedLaw Q)).toReal) ≤
            C * t ^ (-(1 / 2 + (d : ℝ) / 4))

end EinsteinFull.Blueprint
