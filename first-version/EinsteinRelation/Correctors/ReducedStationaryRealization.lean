import EinsteinRelation.Correctors.P53SourceSkewStationaryRepresentative
import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport
import EinsteinRelation.Correctors.CanonicalColumnCovariance
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Stationary realization on the actual reduced law

Source: `paper/main.tex:800–808`. A covariant spatial field on physical
regular environments determines a measurable observable on the actual
reduced environment law. The inverse of the physical reduction transports
the field, and the existing smooth-average representative identifies its
orbit. The extension outside the full-measure physical image has no effect
on that identity.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- A jointly measurable scalar field on physical regular environments has
a jointly measurable extension along the injective physical reduction.
Source: `paper/main.tex:800–808`. -/
theorem exists_reduced_spatial_extension {d : ℕ} {L : ℝ}
    (F : PhysicalField d L → Vec d → ℝ)
    (hF : Measurable (fun p : PhysicalField d L × Vec d => F p.1 p.2)) :
    ∃ H : FieldPair d → Vec d → ℝ,
      Measurable (fun p : FieldPair d × Vec d => H p.1 p.2) ∧
      ∀ (ω : PhysicalField d L) (x : Vec d), H (reduce ω.1) x = F ω x := by
  let e := physicalReduceHomeomorph (d := d) (L := L)
  have hsub : MeasurableEmbedding
      (Subtype.val : ReducedPhysicalField d L → FieldPair d) :=
    MeasurableEmbedding.subtype_coe (measurableSet_physicalReducedRange L)
  have hm : Measurable (fun p : ReducedPhysicalField d L × Vec d => F (e.symm p.1) p.2) :=
    hF.comp ((e.symm.measurable.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨H,hH,he⟩ := (hsub.prodMap MeasurableEmbedding.id).exists_measurable_extend hm
    (fun _ => inferInstance)
  refine ⟨fun ρ x => H (ρ,x),hH,?_⟩
  intro ω x
  have h := congrFun he (e ω,x)
  simpa only [Function.comp_apply, Prod.map_apply, id_eq, Homeomorph.symm_apply_apply] using h

/-- A covariant physical spatial field is the orbit of a measurable reduced
observable. No point evaluation of a spatial a.e. class is used.
Source: `paper/main.tex:800–808`. -/
theorem exists_reduced_stationary_realization {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (F : PhysicalField d L → Vec d → ℝ)
    (hF : Measurable (fun p : PhysicalField d L × Vec d => F p.1 p.2))
    (hloc : ∀ᵐ ω ∂physicalReferenceLaw Q, LocallyIntegrable (F ω) volume)
    (hcov : ∀ z : Vec d, ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      F (physicalTranslate z ω) x = F ω (x+z)) :
    ∃ f : FieldPair d → ℝ, Measurable f ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        f (translate x (reduce ω.1)) = F ω x := by
  obtain ⟨H,hH,he⟩ := exists_reduced_spatial_extension F hF
  have hemb : MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  have hlocH : ∀ᵐ ρ ∂reducedEnvironmentLaw Q, LocallyIntegrable (H ρ) volume := by
    rw [← (measurePreserving_physicalReduction Q).map_eq]
    apply hemb.ae_map_iff.mpr
    filter_upwards [hloc] with ω hω
    simpa only [funext (he ω)] using hω
  have hcovH (z : Vec d) : ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
      ∀ᵐ x ∂(volume : Measure (Vec d)), H (translate z ρ) x = H ρ (x+z) := by
    rw [← (measurePreserving_physicalReduction Q).map_eq]
    apply hemb.ae_map_iff.mpr
    filter_upwards [hcov z] with ω hω
    filter_upwards [hω] with x hx
    rw [← reduce_translate, show translate z ω.1 = (physicalTranslate z ω).1 from rfl,
      he,he]
    exact hx
  refine ⟨stationaryRepresentative H,measurable_stationaryRepresentative hH,?_⟩
  filter_upwards [(measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_orbit_stationaryRepresentative (reducedEnvironmentLaw Q) hH hlocH hcovH)] with ω hω
  simpa only [he] using hω

private theorem locallyIntegrable_dilate {d : ℕ} {F : Vec d → ℝ}
    (hF : LocallyIntegrable F volume) {r : ℝ} (hr : r ≠ 0) :
    LocallyIntegrable (fun x => F (r • x)) volume := by
  let e : Vec d ≃ₜ Vec d := Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit
  have hm : LocallyIntegrable F (Measure.map (fun x : Vec d => r • x) volume) := by
    rw [Measure.map_addHaar_smul volume hr]
    intro x
    obtain ⟨S,hS,hI⟩ := hF x
    refine ⟨S,hS,?_⟩
    rw [IntegrableOn,Measure.restrict_smul]
    exact hI.smul_measure ENNReal.ofReal_ne_top
  exact (locallyIntegrable_map_homeomorph e).mp hm

/-- Real covariance on the actual normalized coefficient law gives a
stationary observable on the reduced law, with the physical spatial scale
restored. Source: `paper/main.tex:693–702,800–808`. -/
theorem exists_reduced_realization_of_covariant_coefficient_field
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (F : Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ)
    (hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      Vec d => F p.1 p.2))
    (hloc : ∀ᵐ A ∂actualCoefficientLaw Q, LocallyIntegrable (F A) volume)
    (hcov : ∀ z : Vec d, ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ x ∂(volume : Measure (Vec d)), F (translateCoefficient z A) x = F A (x+z)) :
    ∃ f : FieldPair d → ℝ, Measurable f ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        f (translate x (reduce ω.1)) =
          F (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) := by
  have hr : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
  let P := project (d := d) (r₀ := r₀) Q.ellipticity_parameter
  let H (ω : PhysicalField d L) (x : Vec d) := F (P ω) (r₀⁻¹ • x)
  have hH : Measurable (fun p : PhysicalField d L × Vec d => H p.1 p.2) :=
    hF.comp (((measurable_project Q.ellipticity_parameter).comp measurable_fst).prodMk
      (measurable_const.smul measurable_snd))
  have hlocH : ∀ᵐ ω ∂physicalReferenceLaw Q, LocallyIntegrable (H ω) volume := by
    filter_upwards [(measurePreserving_akmProject Q).quasiMeasurePreserving.ae hloc] with ω hω
    exact locallyIntegrable_dilate hω (inv_ne_zero hr)
  have hcovH (z : Vec d) : ∀ᵐ ω ∂physicalReferenceLaw Q,
      ∀ᵐ x ∂(volume : Measure (Vec d)), H (physicalTranslate z ω) x = H ω (x+z) := by
    filter_upwards [(measurePreserving_akmProject Q).quasiMeasurePreserving.ae
      (hcov (r₀⁻¹ • z))] with ω hω
    have he : translateCoefficient (r₀⁻¹ • z) (P ω) = P (physicalTranslate z ω) := by
      simpa only [P,smul_smul,mul_inv_cancel₀ hr,one_smul] using
        project_translation_covariant (r₀ := r₀) Q.ellipticity_parameter (r₀⁻¹ • z) ω
    filter_upwards [(Measure.quasiMeasurePreserving_smul
      (volume : Measure (Vec d)) (inv_ne_zero hr)).ae hω] with x hx
    change F (translateCoefficient (r₀⁻¹ • z) (P ω)) (r₀⁻¹ • x) =
      F (P ω) (r₀⁻¹ • x + r₀⁻¹ • z) at hx
    rw [he] at hx
    simpa only [H,smul_add] using hx
  exact exists_reduced_stationary_realization Q H hH hlocH hcovH

/-- The actual zero-based integrated column gradient has a measurable
stationary realization on the reduced law. Its spatial representative is
the original integral, with the inverse finite-range scaling.
Source: `paper/main.tex:800–808`. -/
theorem exists_reduced_integrated_gradient_realization
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      External.AKM.IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      External.AKM.HasCanonicalKernelRepresentation A
        (fun x => (A x).mulVec (unitVector i)) (u A))
    {T : ℝ} (hT : 0 < T) :
    ∃ Y : FieldPair d → Vec d, Measurable Y ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        Y (translate x (reduce ω.1)) =
          fun j => ∫ t in Set.Ioo 0 T,
            G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j := by
  have hex (j : Fin d) : ∃ f : FieldPair d → ℝ, Measurable f ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        f (translate x (reduce ω.1)) =
          ∫ t in Set.Ioo 0 T,
            G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j := by
    let F (A : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) :=
      ∫ t in Set.Ioo 0 T, G A (t,x) j
    have hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
        Vec d => F p.1 p.2) := by
      have hm : Measurable (fun p :
          (Coefficient d (AKMUpperEllipticity L) × Vec d) × ℝ =>
          G p.1.1 (p.2,p.1.2) j) :=
        (measurable_pi_apply j).comp (hG.comp
          (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd)))
      exact hm.stronglyMeasurable.integral_prod_right'.measurable
    have hloc : ∀ᵐ A ∂actualCoefficientLaw Q, LocallyIntegrable (F A) volume := by
      filter_upwards [ae_actual_column_zero_time_weak_equations Q i u G hflow] with A hA
      exact locallyIntegrableOn_univ.mp (((hA T hT).1 j).2.1)
    have hcov (z : Vec d) : ∀ᵐ A ∂actualCoefficientLaw Q,
        ∀ᵐ x ∂(volume : Measure (Vec d)), F (translateCoefficient z A) x = F A (x+z) := by
      filter_upwards [ae_actual_column_flow_and_integrated_gradient_covariant
        Q i u G hflow z] with A hA
      filter_upwards [hA.2 T hT] with x hx
      simpa only [F,add_comm] using congrFun hx j
    exact exists_reduced_realization_of_covariant_coefficient_field Q F hF hloc hcov
  choose f hf he using hex
  refine ⟨fun ρ j => f j ρ,measurable_pi_lambda _ hf,?_⟩
  filter_upwards [ae_all_iff.mpr he] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with x hx
  exact funext hx

end EinsteinRelation.Correctors
