import EinsteinRelation.Correctors.PlanarAffineReference
import EinsteinRelation.Correctors.ConditionalSinglePlanarAmplitude
import EinsteinRelation.Correctors.CenteredAmplitudeIntegrability
import EinsteinRelation.Correctors.ConditionalCenteredMeasurability
import EinsteinRelation.Correctors.StationaryWeightedIntegrals

/-! # Marginal integrability of continuous planar centered correctors

Source: `paper/main.tex:872–890`. Comparison with a deterministic affine
reference reduces the marginal integrability to the stationary L² energy
of the canonical gradient. No higher gradient moment is needed here.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport
open StationarySpatialRealization
local instance : Fact (2 ≤ 2) := ⟨le_rfl⟩

/-- The spatial RMS of the actual total canonical gradient is integrable
under the environment law. Source: `paper/main.tex:733–735,872–883`. -/
theorem integrable_canonicalTotalGradientRms
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (y : Point d) (s : ℝ) (hs : 0 < s) :
    Integrable (fun ω => vectorRms volume (ball 0 s) (fun x =>
      unitVector i + conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) ω))
      (reducedEnvironmentLaw Q) := by
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let F : FieldPair d → ℝ := fun ω => ‖correctorUnitVector i + G ω‖^2
  have hFm : Measurable F :=
    (measurable_const.add (Lp.stronglyMeasurable G).measurable).norm.pow_const 2
  have hFi : Integrable F (reducedEnvironmentLaw Q) :=
    ((memLp_const (correctorUnitVector i)).add (Lp.memLp G)).norm.integrable_sq
  let ν := volume.restrict (ball (0 : Vec d) s)
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d s hs)).2.ne
  have hprod := integrable_weighted_stationary_prod (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) ν hFm hFi
    (measurable_const : Measurable fun _ => (1 : ℝ)) (integrable_const 1)
    (measurable_id.add measurable_const : Measurable fun x : Vec d => x+y.ofLp)
  have hi : Integrable (fun ω => ⨍ x in ball 0 s,
      F (translate (x+y.ofLp) ω) ∂volume) (reducedEnvironmentLaw Q) := by
    simpa only [one_smul, average_eq, ν, measureReal_restrict_apply_univ,
      smul_eq_mul, id_eq, one_mul] using
      hprod.integral_prod_right.const_mul (volume.real (ball (0 : Vec d) s))⁻¹
  have hm : Measurable (fun ω => ⨍ x in ball 0 s,
      F (translate (x+y.ofLp) ω) ∂volume) := by
    have hjoint : Measurable (fun p : FieldPair d × Vec d =>
        F (translate (p.2+y.ofLp) p.1)) :=
      hFm.comp (Probability.continuous_translate.measurable.comp
        ((measurable_snd.add measurable_const).prodMk measurable_fst))
    simpa only [average_eq, smul_eq_mul] using
      hjoint.stronglyMeasurable.integral_prod_right'.measurable.const_mul
        ((volume.restrict (ball (0 : Vec d) s)).real Set.univ)⁻¹
  have hsqrt : Integrable (fun ω => Real.sqrt (⨍ x in ball 0 s,
      F (translate (x+y.ofLp) ω) ∂volume)) (reducedEnvironmentLaw Q) := by
    apply (hi.abs.add (integrable_const 1)).mono' hm.sqrt.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖Real.sqrt _‖ ≤ |⨍ x in ball 0 s,
      F (translate (x+y.ofLp) ω) ∂volume| + 1
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have h := le_abs_self (⨍ x in ball 0 s, F (translate (x+y.ofLp) ω) ∂volume)
      nlinarith [sq_nonneg (|⨍ x in ball 0 s, F (translate (x+y.ofLp) ω) ∂volume|)]
  have heq : (fun ω => vectorRms volume (ball 0 s) (fun x =>
      unitVector i + conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) ω)) =
      (fun ω => Real.sqrt (⨍ x in ball 0 s,
        F (translate (x+y.ofLp) ω) ∂volume)) := by
    funext ω
    unfold vectorRms
    congr 1
    apply setAverage_congr_fun (paired_isOpen_ball (0 : Vec d) s).measurableSet
    filter_upwards [] with x
    intro _
    dsimp only [F, G, conditionalCorrectorGradient, spatialRealization]
    rw [TimeChange.euclideanSq_eq_sq_euclideanNorm,
      TimeChange.euclideanNorm_eq_norm_toLp]
    rfl
  rw [heq]
  exact hsqrt

/-- The actual continuous centered scalar and tensor entries are integrable,
including the prescribed center values. Source: `paper/main.tex:886–890`. -/
theorem integrable_planar_centered_correctors
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀)
    (ζ : SourceMollifier 2) (R : ℝ) (hR : 1 ≤ R) (y : Point 2) (i : Fin 2)
    (φ : FieldPair 2 → Point 2 → ℝ) (σ : FieldPair 2 → Vec 2 → Mat 2)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ)
    (hσ : HasHeatSelectedSkewCorrectorColumn (by decide) Q i σ)
    (hc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω))
    (hσm : ∀ a b, Measurable (fun z : FieldPair 2 × Vec 2 => σ z.1 z.2 a b)) :
    Integrable (conditionalCenteredScalar ζ R y φ) (reducedEnvironmentLaw Q) ∧
      ∀ a b, Integrable (fun ω => conditionalCenteredSkew ζ R y σ ω a b)
        (reducedEnvironmentLaw Q) := by
  obtain ⟨C, hC, hb⟩ := ae_single_planar_centered_correctors_le_affine_energy
    h817 hP L planar_affine_reference_equations
  obtain ⟨hmφ, hmσ⟩ := measurable_conditionalCentered_of_joint ζ R y φ σ hφ.1 hσm
  have hi := (integrable_canonicalTotalGradientRms Q i y (2*R) (by linarith)).const_mul (C*R)
  exact integrable_scalar_and_entries_of_joint_bound (reducedEnvironmentLaw Q)
    _ _ _ hmφ hmσ hi _ _ (hb Q ζ R hR y i φ σ hφ hσ hc)

end EinsteinRelation.Correctors
