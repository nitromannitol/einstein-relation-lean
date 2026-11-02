import EinsteinFull.Calculus.C3JointLocalizationSupport
import EinsteinFull.Calculus.C3CoarseSignedMeasurability
import EinsteinFull.Calculus.C1CoarseGaussianEnergyMeasurability
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_joint_u2D_localization

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull EinsteinRelation.External.AKM

/-- Clock approximation, measurability, centering, locality and stationarity
for the selected joint covariance field. -/
theorem covariance_joint_localization_properties :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
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
          (fun ω => covarianceLocalizedField d hd D s δ γ η β h Q r 0 (translate x ω)))) := by
  intro d hd D s δ γ η β h
  constructor
  · intro p
    obtain ⟨C, hC, hb⟩ := covarianceLocalizedClock_physical_tail_bound d hd D s δ γ η β h p
    exact ⟨C, hC, fun Q _ r hr x => hb Q r hr x⟩
  · intro Q _ r hr
    have hrpos : 0 < r := lt_of_lt_of_le
      (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange)) hr
    refine ⟨(covarianceLocalizedField_joint_measurable d hd D s δ γ η β h Q r).aestronglyMeasurable,
      fun x => ?_⟩
    exact ⟨covarianceLocalizedField_memLp_integral d hd D s δ γ η β h Q hrpos x,
      covarianceLocalizedField_exists_local d hd D s δ γ η β h Q r hr x,
      covarianceLocalizedField_translate d hd D s δ γ η β h Q r x⟩

end EinsteinFull.Blueprint
