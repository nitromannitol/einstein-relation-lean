import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport

/-!
# Cell-flux integrability before packaging an AKM corrector

Source: `paper/main.tex:693-702,727-729`. The literal coefficient flux
has an integrable cell average once its reconstructed coefficient and
canonical gradient identities hold. No existing corrector, or its
cell-integrability field, is assumed.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The cell-integrability characterization field follows from actual
coefficient reconstruction and the global canonical gradient identity. -/
theorem akm_cellFlux_integrable_of_global_identification
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (hcoeff : ∀ᵐ a ∂actualCoefficientLaw Q, a.field =ᵐ[volume] (R a : Vec d → Mat d))
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    Integrable (fun a => ∫ x in unitCell d, (a x).mulVec (halfDirection i + g a x))
      (actualCoefficientLaw Q) := by
  let q := fun a : Coefficient d (AKMUpperEllipticity L) =>
    ∫ x in unitCell d, (a x).mulVec (halfDirection i + g a x)
  have hA : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => R p.1 p.2) :=
    continuous_eval.measurable.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hJ : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      (R p.1 p.2).mulVec (halfDirection i + g p.1 p.2)) := by
    exact (show Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) from
      continuous_fst.matrix_mulVec continuous_snd).measurable.comp
        (hA.prodMk (measurable_const.add hg))
  have hqeq : (fun a => ∫ x in unitCell d, (R a x).mulVec (halfDirection i + g a x))
      =ᵐ[actualCoefficientLaw Q] q := by
    filter_upwards [hcoeff] with a ha
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ha] with x hx
    rw [hx]
  have hq : AEStronglyMeasurable q (actualCoefficientLaw Q) :=
    hJ.stronglyMeasurable.integral_prod_right.aestronglyMeasurable.congr hqeq
  let f : FieldPair d → Vec d := fun ω => (canonicalCorrectorFlux Q i ω).ofLp
  let C := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hf : Measurable f := C.continuous.measurable.comp
    (Lp.stronglyMeasurable (canonicalCorrectorFlux Q i)).measurable
  have hfi : Integrable f (reducedEnvironmentLaw Q) :=
    C.integrable_comp (canonicalCorrectorFlux_integrable Q i)
  letI : IsFiniteMeasure (volume.restrict (unitCell d)) :=
    ⟨by simp [volume_akm_unitCell d]⟩
  have hσ : Measurable (fun y : Vec d => r₀ • y) :=
    (continuous_id.const_smul r₀).measurable
  have hsp := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i (σ := fun y => r₀ • y) hσ)
  have hflux : ∀ᵐ ω ∂physicalReferenceLaw Q,
      q (project (r₀ := r₀) Q.ellipticity_parameter ω) =
      (ellipticityScale L / 2) • ∫ y in unitCell d, f (translate (r₀ • y) (reduce ω.1)) := by
    filter_upwards [hid, hsp] with ω hω hs
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hω, ae_restrict_of_ae hs] with y hy hsy
    change ((ellipticityScale L • (reduce ω.1).1 (r₀ • y)).mulVec
      (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) = _
    change _ = (ellipticityScale L / 2) • (canonicalCorrectorFlux Q i
      (translate (r₀ • y) (reduce ω.1))).ofLp
    rw [hsy, ← hy, Matrix.smul_mulVec, Matrix.mulVec_smul]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcell : Integrable (fun ω => ∫ y in unitCell d, f (translate (r₀ • y) ω))
      (reducedEnvironmentLaw Q) := by
    have h := integrable_weighted_stationary_prod (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (volume.restrict (unitCell d)) hf hfi
      (measurable_const : Measurable fun _ => (1 : ℝ)) (integrable_const 1) hσ
    simpa only [one_smul] using h.integral_prod_right
  apply ((measurePreserving_akmProject Q).integrable_comp hq).mp
  apply (((measurePreserving_physicalReduction Q).integrable_comp_of_integrable hcell).smul
    (ellipticityScale L / 2)).congr
  filter_upwards [hflux] with ω hω
  exact hω.symm

end EinsteinRelation.Correctors
