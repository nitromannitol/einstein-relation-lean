import EinsteinRelation.Correctors.CorrectorSourceLocalMomentsFromLiterature
import EinsteinRelation.Correctors.CanonicalConditionalMollifierFields
import EinsteinRelation.Correctors.HeatSelectedSkewEquations
import EinsteinRelation.Correctors.AKMFluxIdentification

/-! # Actual source equations for the common conditional fields

Source: `paper/main.tex:913–938`. The proved source moments supply ordinary
integrability on the conditioning ball. The canonical scalar and heat-selected
skew predicates then give the spatial equations for these same five fields.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- The common conditional fields obey the actual spatial gradient and flux
equations, from the existing literature inputs and the constructed sources.
Source: `paper/main.tex:913–938`. -/
theorem ae_canonicalConditionalMollifierFields_spatial_equations_of_literature
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (hR : 1 ≤ R) (i : Fin d)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    (hu : IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
      (fun ω x => u ω x.ofLp))
    (hS : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i S)
    (hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
    (hSzero : ∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (∫ y, S ω (-y) j k ∂mollifierCenterMeasure d R) = 0) :
    let f := canonicalConditionalMollifierFields Q i R u S
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (orbit f.scalar ω)
        (fun x => f.gradient (translate x ω)) ∧
      HasWeakRowDivergence Set.univ (fun x => f.skew (translate x ω))
        (fun x => (ω.1 x).mulVec (unitVector i + f.gradient (translate x ω)) -
          (expectedCorrectorFlux Q i).ofLp - f.flux (translate x ω)) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let B := {x : Vec d | euclideanNorm x < 32 * R}
  have hvol := ENNReal.toReal_pos_iff.mp
    (paired_ball_volume_pos_finite (d := d) (show 0 < 32 * R by positivity))
  letI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr (by
    simpa only [ball, sub_zero] using hvol.2.ne)
  have hum : StronglyMeasurable (Function.uncurry u) := by
    simpa only [Function.uncurry, WithLp.ofLp_toLp] using
      (hu.1.comp measurable_swap).stronglyMeasurable
  obtain ⟨hui, hSi⟩ := corrector_sources_conditioning_ball_memLp_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
    (p := 2) le_rfl Q hR i u S hu hS hSm hSzero
  have hui' : MemLp (Function.uncurry u) (ENNReal.ofReal 2)
      ((reducedEnvironmentLaw Q).prod (volume.restrict B)) := by
    simpa only [ball, sub_zero] using hui
  have hSi' (j k : Fin d) : MemLp (fun z : FieldPair d × Vec d => S z.1 z.2 j k)
      (ENNReal.ofReal 2) ((reducedEnvironmentLaw Q).prod (volume.restrict B)) := by
    simpa only [ball, sub_zero] using hSi j k
  apply ae_canonicalConditionalMollifierFields_spatial_equations Q i hR0 u S hum hSm
    (hui'.integrable (by norm_num)) (fun j k => (hSi' j k).integrable (by norm_num))
  · filter_upwards [hu.2] with ω hω
    obtain ⟨_, hgrad, _⟩ := hω
    exact hasWeakGradient_mono (Set.subset_univ _) hgrad
  · filter_upwards [hS.ae_hasWeakRowDivergence,
      ae_spatial_canonicalCorrectorFlux Q i (σ := id) measurable_id] with ω hdiv hflux
    apply hasWeakRowDivergence_mono (Set.subset_univ _)
    apply hasWeakRowDivergence_congr_ae isOpen_univ hdiv Filter.EventuallyEq.rfl
    filter_upwards [ae_restrict_of_ae hflux] with x hx
    change (canonicalCorrectorFlux Q i (translate x ω)).ofLp -
      (expectedCorrectorFlux Q i).ofLp = _
    simp only [id_eq] at hx
    rw [hx]
    rfl

end EinsteinRelation.Correctors
