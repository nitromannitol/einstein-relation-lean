import EinsteinRelation.Correctors.CorrectorConditionalContinuous
import EinsteinRelation.Correctors.PlanarEnergyFromGradientCopies
import EinsteinRelation.Correctors.CorrectorGradientMomentsFromLiterature

/-! # Continuous conditional estimates from point-gradient copy moments

Source: `paper/main.tex:774–786,834–894`. Nested conditioning supplies the
planar spatial energy estimate from the point-gradient estimate. The latter
remains an internal obligation of the conditional-corrector argument.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance gradientCopiesRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Point-gradient copy moments imply both paired-energy estimates; the
planar estimate follows from nested conditioning and Lemma 5.1.
Source: `paper/main.tex:834–894`. -/
theorem conditionalPairEnergyBounds_of_gradient_copy_bounds
    (H51 : CorrectorGradientMoments)
    (hgradient : ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ m : ℝ), 2 ≤ m →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R →
        ∀ (y : Point d) (i : Fin d),
          eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
            (FieldPair d × FieldPair d) => euclideanNorm
            (conditionalCorrectorGradient Q i y z.2.1 -
              conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
            (reducedConditionalCopyLaw (reducedEnvironmentLaw Q)
              (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (B * R ^ (-(d : ℝ)/2))) :
    ConditionalPairEnergyBounds := by
  refine ⟨hgradient, ?_⟩
  intro L r₀ m hm
  letI : Fact (2 ≤ 2) := ⟨by decide⟩
  obtain ⟨C, _, hC⟩ := hgradient 2 L r₀ m hm
  have hplanar := fun (Q : EnvironmentLaw 2 L r₀) (R : ℝ) (hR : 1 ≤ R)
      (y : Point 2) (i : Fin 2) => hC Q R hR y i
  simp only [Nat.cast_ofNat, show -(2 : ℝ)/2 = -1 by norm_num, Real.rpow_neg_one,
    ← div_eq_mul_inv] at hplanar
  obtain ⟨B, hB, hb⟩ := exists_planar_copy_energy_bound_of_gradient_copy_bounds
    H51 L r₀ m hm ⟨C, hplanar⟩
  exact ⟨B, hB.le, hb⟩

/-- The continuous successor of Lemma 5.2 needs only the sharp
point-gradient copy estimate once Lemma 5.1 has been supplied.
Source: `paper/main.tex:774–786,834–894`. -/
theorem correctorConditionalContinuous_of_gradient_copy_bounds
    (h68 : External.AKM.FluxGradientEstimate)
    (h817 : External.GilbargTrudinger.LocalBoundednessEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (H51 : CorrectorGradientMoments)
    (hgradient : ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ m : ℝ), 2 ≤ m →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R →
        ∀ (y : Point d) (i : Fin d),
          eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
            (FieldPair d × FieldPair d) => euclideanNorm
            (conditionalCorrectorGradient Q i y z.2.1 -
              conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
            (reducedConditionalCopyLaw (reducedEnvironmentLaw Q)
              (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (B * R ^ (-(d : ℝ)/2))) :
    CorrectorConditionalContinuousStatement := by
  exact correctorConditionalContinuous_of_pairEnergyBounds h68 h817 hP
    (conditionalPairEnergyBounds_of_gradient_copy_bounds H51 hgradient)

/-- Lemma 5.2 with the gradient moments discharged by the existing AKM
and GT inputs. The sharp point-gradient copy estimate is the remaining
internal hypothesis. Source: `paper/main.tex:735–739,774–786,834–894`. -/
theorem correctorConditionalContinuous_of_literature_and_gradient_copy_bounds
    (h45 : External.AKM.ScalarStationaryEstimate)
    (h46 : External.AKM.ScalarPlanarL2Estimate)
    (h68 : External.AKM.FluxGradientEstimate)
    (h614 : External.AKM.FluxStationaryEstimate)
    (h615 : External.AKM.FluxPlanarL2Estimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (h817 : External.GilbargTrudinger.LocalBoundednessEstimate)
    (h832 : External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : External.GilbargTrudinger.InteriorRegularRepresentative)
    (hgradient : ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ m : ℝ), 2 ≤ m →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R →
        ∀ (y : Point d) (i : Fin d),
          eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
            (FieldPair d × FieldPair d) => euclideanNorm
            (conditionalCorrectorGradient Q i y z.2.1 -
              conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
            (reducedConditionalCopyLaw (reducedEnvironmentLaw Q)
              (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (B * R ^ (-(d : ℝ)/2))) :
    CorrectorConditionalContinuousStatement := by
  exact correctorConditionalContinuous_of_gradient_copy_bounds h68 h817 hP
    (correctorGradientMoments_of_literature h45 h46 h68 h614 h615 hP h817 h832 h836)
    hgradient

end EinsteinRelation.Correctors
