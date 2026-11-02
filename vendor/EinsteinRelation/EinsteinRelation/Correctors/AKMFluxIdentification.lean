import EinsteinRelation.Correctors.AKMSpatialRescaling
import EinsteinRelation.Correctors.StationaryWeightedIntegrals
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Expected flux after the AKM spatial identification

Source: `paper/main.tex:693-702,727-729`; AKM Remark 3.18, (3.93), p. 101.
The expected cell flux and its half-direction normalization follow from a
full-space gradient identification. This is an internal transport lemma;
it does not assume that a lattice-stationary source corrector has a
continuously stationary origin representative.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The physical-reference reduction has precisely the ambient reduced law. -/
theorem measurePreserving_physicalReduction {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    MeasurePreserving (fun ω : PhysicalField d L => reduce ω.1)
      (physicalReferenceLaw Q) (reducedEnvironmentLaw Q) := by
  refine ⟨Probability.measurable_reduce.comp measurable_subtype_coe, ?_⟩
  change Measure.map (reduce ∘ Subtype.val) (physicalReferenceLaw Q) =
    Measure.map reduce Q.measure
  rw [← Measure.map_map Probability.measurable_reduce measurable_subtype_coe,
    physicalReferenceLaw_forget Q]

/-- The canonical L² flux agrees samplewise with the literal spatial
coefficient flux, simultaneously almost everywhere in space. -/
theorem ae_spatial_canonicalCorrectorFlux {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) {σ : Vec d → Vec d}
    (hσ : Measurable σ) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (canonicalCorrectorFlux Q i (translate (σ x) ω)).ofLp =
        (ω.1 (σ x)).mulVec (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (σ x) ω)).ofLp := by
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let X := correctorAffineField Q i + G
  have h0 : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (canonicalCorrectorFlux Q i ω).ofLp =
        (ω.1 0).mulVec (correctorUnitVector i + G ω).ofLp := by
    filter_upwards [reducedOriginCoefficientAction_coeFn Q X,
      Lp.coeFn_add (correctorAffineField Q i) G,
      Lp.coeFn_const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)]
      with ω hA hsum hc
    change (reducedOriginCoefficientAction Q X ω).ofLp = _
    rw [hA, show X ω = correctorUnitVector i + G ω by
      change (correctorAffineField Q i + G) ω = _
      rw [hsum]
      change (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)) ω + G ω = _
      rw [hc]
      rfl]
  have hm : MeasurableSet {p : Vec d × FieldPair d |
      (canonicalCorrectorFlux Q i (translate (σ p.1) p.2)).ofLp =
        (p.2.1 (σ p.1)).mulVec (correctorUnitVector i + G (translate (σ p.1) p.2)).ofLp} := by
    have ht : Measurable (fun p : Vec d × FieldPair d => translate (σ p.1) p.2) :=
      Probability.continuous_translate.measurable.comp
        ((hσ.comp measurable_fst).prodMk measurable_snd)
    have hf := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      ((Lp.stronglyMeasurable (canonicalCorrectorFlux Q i)).measurable.comp ht)
    have hg : Measurable (fun p : Vec d × FieldPair d =>
        (correctorUnitVector i + G (translate (σ p.1) p.2)).ofLp) :=
      (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
        (measurable_const.add ((Lp.stronglyMeasurable G).measurable.comp ht))
    have ha : Measurable (fun p : Vec d × FieldPair d => p.2.1 (σ p.1)) := by
      have h := ((continuous_eval_const (0 : Vec d)).comp continuous_fst).measurable.comp ht
      simpa only [Function.comp_def, translate_matrix, add_zero] using h
    apply measurableSet_eq_fun hf
    unfold Matrix.mulVec dotProduct
    fun_prop
  apply (Measure.ae_ae_comm hm).1
  exact ae_of_all _ fun x => by
    have h := (measurePreserving_translate (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (σ x)).quasiMeasurePreserving.ae h0
    simpa only [translate_matrix, add_zero] using h

/-- The source expected cell flux is the canonical expected flux times
`κ/2`, once the source gradient is identified at all spatial points a.e. -/
theorem akm_meanFlux_of_global_gradient_identification {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    meanFlux φ = (ellipticityScale L / 2) • (expectedCorrectorFlux Q i).ofLp := by
  let f : FieldPair d → Vec d := fun ω => (canonicalCorrectorFlux Q i ω).ofLp
  let C := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hf : Measurable f := C.continuous.measurable.comp
    (Lp.stronglyMeasurable (canonicalCorrectorFlux Q i)).measurable
  have hfi : Integrable f (reducedEnvironmentLaw Q) :=
    C.integrable_comp (canonicalCorrectorFlux_integrable Q i)
  have hvol := volume_akm_unitCell d
  letI : IsFiniteMeasure (volume.restrict (unitCell d)) := ⟨by simp [hvol]⟩
  have hw : Integrable (fun _ : Vec d => (1 : ℝ)) (volume.restrict (unitCell d)) :=
    integrable_const 1
  have hσ : Measurable (fun y : Vec d => r₀ • y) :=
    (continuous_id.const_smul r₀).measurable
  have hsp := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i
      (σ := fun y => r₀ • y) hσ)
  have hflux : ∀ᵐ ω ∂physicalReferenceLaw Q,
      (∫ y in unitCell d,
        ((project (r₀ := r₀) Q.ellipticity_parameter ω) y).mulVec
          (halfDirection i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) =
      (ellipticityScale L / 2) • ∫ y in unitCell d, f (translate (r₀ • y) (reduce ω.1)) := by
    filter_upwards [hid, hsp] with ω hω hs
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hω, ae_restrict_of_ae hs] with y hy hsy
    change ((ellipticityScale L • (reduce ω.1).1 (r₀ • y)).mulVec
      (halfDirection i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) = _
    change _ = (ellipticityScale L / 2) • (canonicalCorrectorFlux Q i
      (translate (r₀ • y) (reduce ω.1))).ofLp
    rw [hsy, ← hy, Matrix.smul_mulVec, Matrix.mulVec_smul]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hm := integral_map (μ := physicalReferenceLaw Q)
    (measurable_project Q.ellipticity_parameter).aemeasurable φ.cell_integrable.aestronglyMeasurable
  change meanFlux φ = _ at hm ⊢
  rw [hm, integral_congr_ae hflux, integral_smul]
  have hEmb : MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  have hmap := (measurePreserving_physicalReduction Q).integral_comp hEmb
    (fun ω => ∫ y in unitCell d, f (translate (r₀ • y) ω))
  rw [hmap]
  have hmean := integral_weighted_stationary (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (volume.restrict (unitCell d)) hf hfi
    (measurable_const : Measurable fun _ : Vec d => (1 : ℝ)) hw
    (σ := fun y => r₀ • y) hσ
  have he : (∫ ω, f ω ∂reducedEnvironmentLaw Q) = (expectedCorrectorFlux Q i).ofLp :=
    C.integral_comp_comm (canonicalCorrectorFlux_integrable Q i)
  simpa only [one_smul, integral_const, Measure.real, Measure.restrict_apply_univ,
    hvol, ENNReal.toReal_one, smul_eq_mul, one_mul, he] using
    congrArg ((ellipticityScale L / 2) • ·) hmean

/-- The exact scalar center required by the AKM energy-transfer interface
is a consequence of the global gradient identification. -/
theorem akm_meanFlux_halfDirection_of_global_gradient_identification
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    dot (halfDirection i) (meanFlux φ) = ellipticityScale L / 4 *
      dot (unitVector i) ((homogenizedMatrix Q).mulVec (unitVector i)) := by
  rw [akm_meanFlux_of_global_gradient_identification Q i φ hid]
  have hc : (homogenizedMatrix Q).mulVec (unitVector i) = (expectedCorrectorFlux Q i).ofLp := by
    ext j
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, homogenizedMatrix, mul_ite]
  rw [hc]
  unfold halfDirection dot
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end EinsteinRelation.Correctors

