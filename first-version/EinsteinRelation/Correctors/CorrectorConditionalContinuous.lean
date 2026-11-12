import EinsteinRelation.Correctors.ConditionalMomentInputs
import EinsteinRelation.Correctors.ConditionalPlanarAEMoments
import EinsteinRelation.Correctors.ContinuousSkewCenteredMeasurability
import EinsteinRelation.Correctors.ConditionalPairEnergyBounds
import EinsteinRelation.Correctors.ContinuousCenteredIntegrability

/-! Source: `paper/main.tex:774-786,834-894`. Assembly of the continuous
successor of Lemma 5.2 from sharp paired moments and centered marginal
integrability. The analytic obligations are internal and remain explicit. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.GilbargTrudinger NormalizedSpatialRepresentativeSupport HeatSelectedSkewMeaning
open NormalizedScalarPhysicalLawTransportSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance continuousFact : Fact (2 ≤ 2) := ⟨by decide⟩
local instance conditionalContinuousRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The exact continuous successor of Lemma 5.2 follows from the internal
moment obligations and measurability of the centered planar skew field.
Source: `paper/main.tex:774-786,834-894`. -/
theorem correctorConditionalContinuous_of_moments_and_centered_measurability
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    (hMom : ConditionalMomentInputs)
    (hSm : ∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (ζ : SourceMollifier 2)
      (R : ℝ) (_hR : 1 ≤ R) (y : Point 2) (i : Fin 2)
      (σ : FieldPair 2 → Vec 2 → Mat 2),
      HasHeatSelectedSkewCorrectorColumn (by decide) Q i σ →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (σ ω)) →
      AEStronglyMeasurable (conditionalCenteredSkew ζ R y σ) (reducedEnvironmentLaw Q)) :
    CorrectorConditionalContinuousStatement := by
  intro d hd L r₀ ζ m hm
  obtain ⟨B, -, hB⟩ := hMom.1 d L r₀ m hm
  obtain ⟨D, hD, hEnergy⟩ := hMom.2.1 L r₀ m hm
  obtain ⟨A, -, hPlanar⟩ := paired_planar_centered_moments_of_energy_ae h817 hP L
  refine ⟨max B (A*D), ?_⟩
  intro Q R hR y i φ σ hφ hσ hc
  dsimp only
  have hU := isOpen_conditionalCorrectorBall R y
  have hp : 1 ≤ ENNReal.ofReal m := ENNReal.one_le_ofReal.mpr (by linarith)
  constructor
  · exact (eLpNorm_canonicalGradient_euclidean_conditional_error_le_copy_difference Q i
      (WithLp.ofLp y) (conditionalCorrectorBall R y) hU hp ENNReal.ofReal_ne_top).trans
      ((hB Q R hR y i).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_max_left B (A*D)) (Real.rpow_nonneg (by linarith) _))))
  · intro hd2
    subst d
    obtain ⟨hφf, hσf⟩ := hMom.2.2 Q ζ R hR y i φ σ hφ hσ hc
    have hφm := (measurable_conditionalCentered_of_joint ζ R y φ
      (fun _ _ => 0) hφ.1 (fun _ _ => measurable_const)).1
    have hσm := hSm Q ζ R hR y i σ hσ (hc.mono fun _ h => h.2)
    have hφi : Integrable (conditionalCenteredScalar ζ R y φ) (reducedEnvironmentLaw Q) :=
      ⟨hφm.aestronglyMeasurable, hφf⟩
    have hσi (a b : Fin 2) : Integrable
        (fun ω => conditionalCenteredSkew ζ R y σ ω a b) (reducedEnvironmentLaw Q) :=
      ⟨(show Continuous (fun A : Mat 2 => A a b) by fun_prop).comp_aestronglyMeasurable hσm,
        hσf a b⟩
    obtain ⟨hE, hEb⟩ := hEnergy Q R hR y i
    obtain ⟨-, -, hCopies⟩ := hPlanar Q ζ R hR y i φ σ hφ hσ hc hσm
      (ENNReal.ofReal m) D hD hE hEb
    exact (add_le_add
      (eLpNorm_reduced_conditional_error_le_copy_difference_ae (reducedEnvironmentLaw Q)
        (conditionalCorrectorBall R y) hU hp ENNReal.ofReal_ne_top hφm.aestronglyMeasurable hφi)
      (eLpNorm_reduced_conditional_frobenius_le_copy_difference_ae (reducedEnvironmentLaw Q)
        (conditionalCorrectorBall R y) hU hp ENNReal.ofReal_ne_top hσm hσi)).trans
      (hCopies.trans (ENNReal.ofReal_le_ofReal (le_max_right B (A*D))))

/-- The production twin of `corrector.conditional` (Lemma 5.2), conditional on the
explicit internal paired-moment and marginal-integrability obligations.
Its external hypotheses are the cited flux, local boundedness and
Poincare estimates. This is a reduction, not a proof of the internal
moment obligations. Source: `paper/main.tex:774-786,834-894`. -/
theorem correctorConditionalContinuous_of_internal_moments
    (h68 : External.AKM.FluxGradientEstimate)
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    (hMom : ConditionalMomentInputs) : CorrectorConditionalContinuousStatement := by
  apply correctorConditionalContinuous_of_moments_and_centered_measurability h817 hP hMom
  intro L r₀ Q ζ R hR y i σ hσ hc
  exact aestronglyMeasurable_conditionalCenteredSkew_of_continuous
    h68 hP Q ζ R hR y i σ hσ hc

/-- Stationary L² energy and the affine comparison discharge the marginal
integrability clause; only the two sharp paired-energy estimates remain.
Source: `paper/main.tex:834-894`. -/
theorem conditionalMomentInputs_of_pairEnergyBounds
    (h68 : External.AKM.FluxGradientEstimate)
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    (hEnergy : ConditionalPairEnergyBounds) : ConditionalMomentInputs := by
  refine ⟨hEnergy.1, hEnergy.2, ?_⟩
  intro L r₀ Q ζ R hR y i φ σ hφ hσ hc
  obtain ⟨hφi, hσi⟩ := integrable_planar_centered_correctors_of_continuous
    h68 h817 hP Q ζ R hR y i φ σ hφ hσ hc
  exact ⟨hφi.hasFiniteIntegral, fun a b => (hσi a b).hasFiniteIntegral⟩

/-- The exact continuous production successor of Lemma 5.2, conditional
on the sharp point-gradient and planar ball-energy copy estimates.
Centered skew measurability and all centered marginal integrability
are proved here from the cited flux, local boundedness and Poincare
estimates. The two paired-energy estimates are internal obligations,
not assumed literature. Source: `paper/main.tex:774-786,834-894`. -/
theorem correctorConditionalContinuous_of_pairEnergyBounds
    (h68 : External.AKM.FluxGradientEstimate)
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    (hEnergy : ConditionalPairEnergyBounds) : CorrectorConditionalContinuousStatement := by
  exact correctorConditionalContinuous_of_internal_moments h68 h817 hP
    (conditionalMomentInputs_of_pairEnergyBounds h68 h817 hP hEnergy)

end EinsteinRelation.Correctors
