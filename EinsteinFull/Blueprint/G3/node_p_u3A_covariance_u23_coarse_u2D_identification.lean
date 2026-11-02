import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Graph node `p:covariance#coarse-identification`, `paper/main.tex:874–885`.
DRAFT. The coefficient is the genuine A₁ polarization at the normalized physical
coefficient. Its homogenized load is explicitly scaled, not chosen from an
estimate. The isotropic source Gaussian and all matrix entries are retained.
One constant precedes the law; the physical source scale is at least one. -/
def node_p_u3A_covariance_u23_coarse_u2D_identificationStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ D : StructuralData d,
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ r : ℝ, D.dependenceRange ≤ r → ∀ x : Vec d,
      let error := fun ω : FieldPair d => fun a : JointObservationIndex d =>
        match a with
        | .inl (j,k) => (∫ z : Vec d, heatKernel 0 r z *
            commutatorObservation Q j k (translate (x - z) ω)) -
            covarianceCenteredCoarseEntry D Q r x j k ω
        | .inr _ => 0
      (∀ j k : Fin d,
        (∀ᵐ ω ∂reducedLaw Q, Integrable (fun z : Vec d =>
          heatKernel 0 r z * commutatorObservation Q j k (translate (x - z) ω))) ∧
        MemLp (covarianceCoarseEntry D Q r x j k) 2 (reducedLaw Q)) ∧
      MemLp (fun ω => covarianceVectorSize (error ω)) 2 (reducedLaw Q) ∧
      covarianceL2Size (reducedLaw Q) error ≤ C * r ^ (-(d : ℝ))

end EinsteinFull.Blueprint
