import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Graph node `p:covariance#joint-localization`, `paper/main.tex:905–909`.
DRAFT. The selected family is the genuine reviewed coordinate minimization.
Local representatives, product measurability, stationarity and centering are
conclusions, not choice fields. Locality observes both actual reduced fields.
The source r≥2 restriction becomes r≥2 times the physical dependence range.
All fixed-power clock-error constants precede the law. -/
def node_p_u3A_covariance_u23_joint_u2D_localizationStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
    ∃ C : ℝ, 0 < C ∧
    (∀ p : ℝ, ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ r : ℝ, 2 * D.dependenceRange ≤ r →
        ∀ x : Vec d,
        ∀ᵐ ω ∂reducedLaw Q,
          |(∫ z : Vec d, heatKernel 0 r z * centeredClockField Q (x - z) ω) -
            covarianceLocalizedField d hd D s δ γ η β h Q r x ω (.inr ())| ≤
              Cₚ * r ^ (-p)) ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ r : ℝ, 2 * D.dependenceRange ≤ r →
      AEStronglyMeasurable
        (fun p : Vec d × FieldPair d => covarianceLocalizedField d hd D s δ γ η β h Q r p.1 p.2)
        (volume.prod (reducedLaw Q)) ∧
      (∀ x : Vec d,
        (∀ a : JointObservationIndex d,
          MemLp (fun ω => covarianceLocalizedField d hd D s δ γ η β h Q r x ω a) 2 (reducedLaw Q) ∧
          (∫ ω, covarianceLocalizedField d hd D s δ γ η β h Q r x ω a ∂reducedLaw Q) = 0) ∧
        (∃ localized : FieldPair d → JointObservationIndex d → ℝ,
          @Measurable _ _ (EinsteinRelation.localSigma
            (ball x (covarianceLocalizationRadius D δ r))) inferInstance localized ∧
          localized =ᵐ[reducedLaw Q] covarianceLocalizedField d hd D s δ γ η β h Q r x) ∧
        ((fun ω => covarianceLocalizedField d hd D s δ γ η β h Q r x ω) =ᵐ[reducedLaw Q]
          (fun ω => covarianceLocalizedField d hd D s δ γ η β h Q r 0 (translate x ω))) ∧
        let error := fun ω : FieldPair d => fun a : JointObservationIndex d =>
          match a with
          | .inl (j,k) => covarianceLocalizedField d hd D s δ γ η β h Q r x ω a -
              covarianceCenteredCoarseEntry D Q r x j k ω
          | .inr _ => 0
        MemLp (fun ω => covarianceVectorSize (error ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) error ≤ C * r ^ (-γ))

end EinsteinFull.Blueprint
