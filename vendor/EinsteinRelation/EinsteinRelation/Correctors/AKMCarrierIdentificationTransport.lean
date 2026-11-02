import EinsteinRelation.Correctors.AKMCanonicalGradientCandidate
import EinsteinRelation.Correctors.AKMFluxIdentification

/-!
# Transport between the AKM carrier and the reduced coefficient law

Source: `paper/main.tex:693-702,727-729`. Reconstructing and undoing the
normalization pushes the actual AKM law to the coefficient marginal of the
reduced law. Consequently coefficient factors preserve their genuine L²
classes and the canonical factor belongs to the actual potential domain.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- The literal coefficient project map preserves the actual laws. -/
theorem measurePreserving_akmProject {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    MeasurePreserving (project (r₀ := r₀) Q.ellipticity_parameter)
      (physicalReferenceLaw Q) (actualCoefficientLaw Q) :=
  ⟨measurable_project Q.ellipticity_parameter, rfl⟩

/-- The actual AKM law is invariant under every real spatial translation. -/
theorem actualCoefficientLaw_translation_invariant_real {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (z : Vec d) :
    Measure.map (translateCoefficient z) (actualCoefficientLaw Q) =
      actualCoefficientLaw Q := by
  change Measure.map (translateCoefficient z)
      (Measure.map (project (r₀ := r₀) Q.ellipticity_parameter)
        (physicalReferenceLaw Q)) = _
  rw [Measure.map_map (measurable_translateCoefficient _)
    (measurable_project Q.ellipticity_parameter)]
  rw [show (translateCoefficient z ∘ project (r₀ := r₀) Q.ellipticity_parameter) =
      (project (r₀ := r₀) Q.ellipticity_parameter ∘ physicalTranslate (r₀ • z)) from by
        funext ω
        exact project_translation_covariant (r₀ := r₀) Q.ellipticity_parameter z ω]
  rw [← Measure.map_map (measurable_project Q.ellipticity_parameter)
    (measurable_physicalTranslate (r₀ • z)), physicalReferenceLaw_translation_invariant Q]
  rfl

/-- Reconstruction sends the actual raw coefficient law to the coefficient
marginal of the actual reduced law, including the inverse spatial dilation. -/
theorem map_akmReducedReconstruction {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩) :
    Measure.map (akmReducedReconstruction r₀ R) (actualCoefficientLaw Q) =
      Measure.map (Prod.fst : FieldPair d → CoefficientField d) (reducedEnvironmentLaw Q) := by
  have hm : Measurable (akmReducedReconstruction r₀ R) :=
    (measurable_rescaleCoefficientField d _ _).comp hR
  have hr : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
  calc
    _ = Measure.map ((akmReducedReconstruction r₀ R) ∘
        project (r₀ := r₀) Q.ellipticity_parameter) (physicalReferenceLaw Q) :=
      Measure.map_map hm (measurable_project Q.ellipticity_parameter)
    _ = Measure.map ((Prod.fst : FieldPair d → CoefficientField d) ∘
        (fun ω : PhysicalField d L => reduce ω.1)) (physicalReferenceLaw Q) := by
      congr 1
      funext ω
      exact akmReducedReconstruction_project Q.ellipticity_parameter hr R hReq ω
    _ = _ := by
      rw [← Measure.map_map continuous_fst.measurable
        (measurePreserving_physicalReduction Q).measurable,
        (measurePreserving_physicalReduction Q).map_eq]

/-- Every measurable coefficient observable has the same L² membership
before and after reconstructing the actual AKM coefficient law. -/
theorem memLp_akmReducedReconstruction_iff {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩)
    {E : Type*} [NormedAddCommGroup E]
    (F : CoefficientField d → E) (hF : StronglyMeasurable F) :
    MemLp (fun a => F (akmReducedReconstruction r₀ R a)) 2 (actualCoefficientLaw Q) ↔
      MemLp (fun ω : FieldPair d => F ω.1) 2 (reducedEnvironmentLaw Q) := by
  have hm : Measurable (akmReducedReconstruction r₀ R) :=
    (measurable_rescaleCoefficientField d _ _).comp hR
  change MemLp (F ∘ akmReducedReconstruction r₀ R) 2 (actualCoefficientLaw Q) ↔ _
  rw [← memLp_map_measure_iff hF.aestronglyMeasurable hm.aemeasurable,
    map_akmReducedReconstruction Q R hR hReq,
    memLp_map_measure_iff hF.aestronglyMeasurable continuous_fst.measurable.aemeasurable]
  rfl

/-- A canonical coefficient factor is the same L² element in the reduced
law and hence belongs to its closed potential-gradient domain. -/
theorem canonical_coefficient_factor_mem_potentialDomain {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (F : CoefficientField d → EuclideanSpace ℝ (Fin d))
    (hFG : (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) =ᵐ[reducedEnvironmentLaw Q]
        fun ω => F ω.1) :
    ∃ hmem : MemLp (fun ω : FieldPair d => F ω.1) 2 (reducedEnvironmentLaw Q),
      hmem.toLp (fun ω => F ω.1) = (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ∧
      hmem.toLp (fun ω => F ω.1) ∈ correctorPotentialDomain Q := by
  have hmem := (Lp.memLp (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).ae_eq hFG
  have heq : hmem.toLp (fun ω => F ω.1) = (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
    apply Lp.ext
    exact hmem.coeFn_toLp.trans hFG.symm
  refine ⟨hmem, heq, ?_⟩
  rw [heq]
  exact (canonicalCorrectorGradient Q i).property

/-- The unscaled AKM origin gradient is an actual L² class. Pulling it back
along the physical project map gives exactly the canonical reduced gradient.
No pointwise origin evaluation of a spatial almost-everywhere identity is used. -/
theorem exists_akm_origin_L2_identification {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ H : Lp (EuclideanSpace ℝ (Fin d)) 2 (actualCoefficientLaw Q),
      Lp.compMeasurePreserving (project (r₀ := r₀) Q.ellipticity_parameter)
        (measurePreserving_akmProject Q) H =
      Lp.compMeasurePreserving (fun ω : PhysicalField d L => reduce ω.1)
        (measurePreserving_physicalReduction Q)
        (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
  obtain ⟨R, hR, hReq⟩ := exists_measurable_continuous_reconstruction
    (d := d) (K := AKMUpperEllipticity L)
  obtain ⟨F, hF, hFG⟩ := exists_coefficient_factor_of_canonicalGradient Q i
  obtain ⟨hmem, _, _⟩ := canonical_coefficient_factor_mem_potentialDomain Q i F hFG
  have hraw := (memLp_akmReducedReconstruction_iff Q R hR hReq F hF).mpr hmem
  refine ⟨hraw.toLp _, ?_⟩
  apply Lp.ext
  have hproj := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hraw.coeFn_toLp
  have hred := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hFG
  filter_upwards [Lp.coeFn_compMeasurePreserving (hraw.toLp _)
      (measurePreserving_akmProject Q),
    Lp.coeFn_compMeasurePreserving (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (measurePreserving_physicalReduction Q), hproj, hred] with ω hp hr he hf
  simp only [Function.comp_def] at hp hr
  rw [hp, hr, he, hf,
    akmReducedReconstruction_project Q.ellipticity_parameter
      (zero_lt_one.trans_le Q.range_parameter).ne' R hReq ω]

end EinsteinRelation.Correctors
