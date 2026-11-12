import EinsteinRelation.Correctors.CanonicalHeatSelectionRescaling
import EinsteinRelation.Correctors.HeatSelectionDilationIdentification
import EinsteinRelation.Correctors.HeatSelectionBallRestriction
import EinsteinRelation.Correctors.AKMCanonicalHeatDilation
import EinsteinRelation.Correctors.ScalarGaugeReconstruction
import EinsteinRelation.Correctors.SpatialWeakDilation

/-! Source: `paper/main.tex:722,741-756`. The raw AKM flux potential,
with its physical amplitude and range, has the canonical selected gradient
and hence agrees with the physical potential modulo constants. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning Environment.AKMTestIntegralSupport ReductionImageV3

/-- The actual rescaled raw potential and any canonical heat-selected
potential have equal weak gradients and differ only by entrywise constants.
Both heat cutoffs are transported through genuine local L² limits. -/
theorem ae_physicalAKMFlux_potential_gauge
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (S : FluxCorrector (scaledAKMCorrector φ 2))
    (hsource : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      centeredFlux (scaledAKMCorrector φ 2)
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
          ellipticityScale L •
            ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
              (expectedCorrectorFlux Q i).ofLp))
    (σ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ j k : Fin d, ∃ c : ℝ,
      (fun x => (r₀ / ellipticityScale L) * S.potential
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k) =ᵐ[volume]
      (fun x => σ (reduce ω.1) x j k + c) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hκ : ellipticityScale L ≠ 0 :=
    (ellipticityScale_pos Q.ellipticity_parameter).ne'
  obtain ⟨F, _, hF⟩ := hσ
  have hrescale := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_canonical_flux_heat_selection_rescaled_local_L2 Q i ((r₀⁻¹) ^ 2)⁻¹
      (by positivity))
  have hcanonical := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hF
  have hselect := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae S.heat_selected
  have hweak := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae S.weak_gradient
  have hlocal := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae
    S.locally_square_integrable
  filter_upwards [hsource, hrescale, hcanonical, hselect, hweak, hlocal]
    with ω hsrc htime hcan hsel hwe hloc
  let g : Vec d → Vec d := fun y =>
    (canonicalCorrectorFlux Q i (translate y (reduce ω.1)) - expectedCorrectorFlux Q i).ofLp
  let G : Fin d → Fin d → Vec d → Vec d :=
    fun j k x l => F (translate x (reduce ω.1)) j k l
  have hG : IsHeatSelectedFluxGradient g G :=
    isHeatSelectedFluxGradient_of_iterated g (reduce ω.1) F hcan.2.1
  have hraw : IsHeatSelectedFluxGradient
      (fun y => ellipticityScale L • g ((r₀⁻¹)⁻¹ • y))
      (S.grad (project (r₀ := r₀) Q.ellipticity_parameter ω)) := by
    apply isHeatSelectedFluxGradient_congr_source_ae ?_ hsel
    simpa only [inv_inv] using hsrc
  have heq := ae_eq_of_heat_selection_dilation g G
    (S.grad (project (r₀ := r₀) Q.ellipticity_parameter ω)) hG r₀⁻¹
    (ellipticityScale L) (inv_pos.mpr hr) (htime G hG) hraw
  intro j k
  have hgrad := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae (heq j k)
  have hu := hasWeakGradient_dilation
    (fun x => S.potential (project (r₀ := r₀) Q.ellipticity_parameter ω) x j k)
    (S.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) j k)
    (fun R hR => (hloc R hR j k).1) (fun R hR => (hloc R hR j k).2)
    (hwe j k) r₀⁻¹ (r₀ / ellipticityScale L) (inv_pos.mpr hr)
  have hu' : HasWeakGradient Set.univ
      (fun x => (r₀ / ellipticityScale L) * S.potential
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k)
      (G j k) := by
    intro l
    apply (hu l).congr_ae (ae_eq_refl _)
    simp only [Measure.restrict_univ]
    filter_upwards [hgrad] with x hx
    have hx' : S.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) j k
        (r₀⁻¹ • x) = ellipticityScale L • G j k x := by
      simpa only [inv_inv, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hx
    change ((r₀ / ellipticityScale L * r₀⁻¹) •
      S.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) j k (r₀⁻¹ • x)) l =
        G j k x l
    rw [hx', smul_smul]
    have hmul : (r₀ / ellipticityScale L * r₀⁻¹) * ellipticityScale L = 1 := by
      field_simp
    rw [hmul, one_smul]
  exact weakPotentials_differ_by_constant
    (by have := (Fact.out : 2 ≤ d); omega) hu' (hcan.2.2 j k)

end EinsteinRelation.Correctors
