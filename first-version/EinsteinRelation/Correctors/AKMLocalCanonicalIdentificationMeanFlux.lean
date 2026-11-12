import EinsteinRelation.Correctors.AKMFluxIdentification
import EinsteinRelation.Environment.AKMReconstructionAgreement

/-! # Canonical identification of the local-corrector mean flux

Source: `paper/main.tex:808-816,948-955`. The local-corrector literature
uses coordinate integrals on the positive unit cube. The same canonical
mean flux is obtained on any finite-volume spatial set. Reconstructed
coefficients justify measurability on the source test-integral sigma algebra.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The expected coordinate flux on any finite-volume set has the canonical
value, with the exact coefficient and half-slope normalization. -/
theorem akmLocal_meanFlux_coordinate_of_canonical_gradient
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i j : Fin d)
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)] :
    Integrable (fun a => ∫ x in U, ((a x).mulVec (halfDirection i + g a x)) j)
      (actualCoefficientLaw Q) ∧
    (∫ a, ∫ x in U, ((a x).mulVec (halfDirection i + g a x)) j
      ∂volume ∂actualCoefficientLaw Q) =
      (volume U).toReal * (ellipticityScale L / 2 * expectedCorrectorFlux Q i j) := by
  obtain ⟨R, hR, hReq⟩ := exists_measurable_continuous_reconstruction
    (d := d) (K := AKMUpperEllipticity L)
  have hcoeff := ae_actualCoefficientLaw_field_eq_reconstruction Q R hR hReq
  let q := fun a : Coefficient d (AKMUpperEllipticity L) =>
    ∫ x in U, ((a x).mulVec (halfDirection i + g a x)) j
  have hA : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => R p.1 p.2) :=
    continuous_eval.measurable.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hJ : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      ((R p.1 p.2).mulVec (halfDirection i + g p.1 p.2)) j) := by
    exact (measurable_pi_apply j).comp
      ((show Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) from
        continuous_fst.matrix_mulVec continuous_snd).measurable.comp
        (hA.prodMk (measurable_const.add hg)))
  have hqeq : (fun a => ∫ x in U, ((R a x).mulVec (halfDirection i + g a x)) j)
      =ᵐ[actualCoefficientLaw Q] q := by
    filter_upwards [hcoeff] with a ha
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ha] with x hx
    rw [hx]
  have hq : AEStronglyMeasurable q (actualCoefficientLaw Q) :=
    hJ.stronglyMeasurable.integral_prod_right.aestronglyMeasurable.congr hqeq
  let f : FieldPair d → ℝ := fun ω => canonicalCorrectorFlux Q i ω j
  let C := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j
  have hf : Measurable f := C.continuous.measurable.comp
    (Lp.stronglyMeasurable (canonicalCorrectorFlux Q i)).measurable
  have hfi : Integrable f (reducedEnvironmentLaw Q) :=
    C.integrable_comp (canonicalCorrectorFlux_integrable Q i)
  have hσ : Measurable (fun y : Vec d => r₀ • y) :=
    (continuous_const.smul continuous_id).measurable
  have hsp := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i (σ := fun y => r₀ • y) hσ)
  have hflux : ∀ᵐ ω ∂physicalReferenceLaw Q,
      q (project (r₀ := r₀) Q.ellipticity_parameter ω) =
      (ellipticityScale L / 2) * ∫ y in U, f (translate (r₀ • y) (reduce ω.1)) := by
    filter_upwards [hid, hsp] with ω hω hs
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hω, ae_restrict_of_ae hs] with y hy hsy
    change ((ellipticityScale L • (reduce ω.1).1 (r₀ • y)).mulVec
      (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) j = _
    change _ = (ellipticityScale L / 2) * (canonicalCorrectorFlux Q i
      (translate (r₀ • y) (reduce ω.1))) j
    rw [congrFun hsy j, ← hy, Matrix.smul_mulVec, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcell : Integrable (fun ω => ∫ y in U, f (translate (r₀ • y) ω))
      (reducedEnvironmentLaw Q) := by
    have h := integrable_weighted_stationary_prod (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (volume.restrict U) hf hfi
      (measurable_const : Measurable fun _ => (1 : ℝ)) (integrable_const 1) hσ
    simpa only [one_smul] using h.integral_prod_right
  have hqi : Integrable q (actualCoefficientLaw Q) := by
    have hπ : MeasurePreserving (project (r₀ := r₀) Q.ellipticity_parameter)
        (physicalReferenceLaw Q) (actualCoefficientLaw Q) :=
      ⟨measurable_project Q.ellipticity_parameter, rfl⟩
    apply (hπ.integrable_comp hq).mp
    apply (((measurePreserving_physicalReduction Q).integrable_comp_of_integrable
      hcell).const_mul (ellipticityScale L / 2)).congr
    filter_upwards [hflux] with ω hω
    exact hω.symm
  refine ⟨hqi, ?_⟩
  have hm := integral_map (μ := physicalReferenceLaw Q)
    (measurable_project Q.ellipticity_parameter).aemeasurable hq
  change (∫ a, q a ∂actualCoefficientLaw Q) = _ at hm
  change (∫ a, q a ∂actualCoefficientLaw Q) = _
  rw [hm, integral_congr_ae hflux, integral_const_mul]
  have hEmb : MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  have hmap := (measurePreserving_physicalReduction Q).integral_comp hEmb
    (fun ω => ∫ y in U, f (translate (r₀ • y) ω))
  rw [hmap]
  have hmean := integral_weighted_stationary (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (volume.restrict U) hf hfi
    (measurable_const : Measurable fun _ : Vec d => (1 : ℝ)) (integrable_const 1)
    (σ := fun y => r₀ • y) hσ
  have he : (∫ ω, f ω ∂reducedEnvironmentLaw Q) = expectedCorrectorFlux Q i j :=
    C.integral_comp_comm (canonicalCorrectorFlux_integrable Q i)
  simp only [one_mul, integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one, he] at hmean
  rw [hmean]
  ring

end EinsteinRelation.Correctors
