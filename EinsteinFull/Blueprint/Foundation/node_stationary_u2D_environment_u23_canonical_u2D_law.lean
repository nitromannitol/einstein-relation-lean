import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `stationary-environment#canonical-law`, `paper/main.tex:236`.
The canonical space is the existing compact-open space of continuous joint
coefficient pairs, with its Borel sigma algebra. No independent clock is added. -/
def node_stationary_u2D_environment_u23_canonical_u2D_lawStmt : Prop :=
  ∀ (d : ℕ) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    (inferInstance : MeasurableSpace (FieldPair d)) = borel (FieldPair d) ∧
    reducedLaw Q = Q.measure.map reduce ∧
    IsProbabilityMeasure (reducedLaw Q) ∧
    Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) ∧
    IsStationary (reducedLaw Q) ∧ HasFiniteRange r₀ (reducedLaw Q) ∧
    ∀ U : Set (Vec d), MeasurableSet U →
      localSigma U ≤ (inferInstance : MeasurableSpace (FieldPair d))

end EinsteinFull.Blueprint
