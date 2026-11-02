import EinsteinRelation.Correctors.AKMCanonicalGradientCandidate

/-!
# Measurable coefficient-factor orbits on the raw carrier

Source: `paper/main.tex:693-702`. Scalar and vector coefficient factors
are evaluated before changing spatial scale. Their raw-carrier orbits
agree with the actual reduced orbits almost everywhere in all of space.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- Evaluate a continuous-coefficient observable along the reconstructed,
unscaled coefficient orbit. -/
def akmUnscaledCoefficientFactor {d : ℕ} {L : ℝ} {E : Type*} (r₀ : ℝ)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (F : CoefficientField d → E)
    (a : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) : E :=
  F (translate x (akmReducedReconstruction r₀ R a, (0 : C(Vec d, ℝ)))).1

/-- Evaluation of a measurable factor along the reconstructed coefficient
orbit is jointly measurable in raw coefficients and space. -/
theorem measurable_akmUnscaledCoefficientFactor {d : ℕ} {L : ℝ} {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (r₀ : ℝ) (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hR : Measurable R) (F : CoefficientField d → E) (hF : Measurable F) :
    Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      akmUnscaledCoefficientFactor r₀ R F p.1 p.2) := by
  rw [BorelSpace.measurable_eq (α := E)] at hF ⊢
  letI : MeasurableSpace C(Vec d, ℝ) := borel _
  letI : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
  have hrec : Measurable (akmReducedReconstruction r₀ R) :=
    (measurable_rescaleCoefficientField d _ _).comp hR
  have hpair : Measurable (fun a =>
      (akmReducedReconstruction r₀ R a, (0 : C(Vec d, ℝ))) :
      Coefficient d (AKMUpperEllipticity L) → FieldPair d) := by
    change @Measurable _ (CoefficientField d × C(Vec d, ℝ)) _ (borel _) _
    rw [← (Prod.borelSpace (α := CoefficientField d) (β := C(Vec d, ℝ))).measurable_eq]
    exact hrec.prodMk measurable_const
  exact hF.comp ((continuous_fst.comp Probability.continuous_translate).measurable.comp
    (measurable_snd.prodMk (hpair.comp measurable_fst)))

/-- Coefficient-factor equality in the reduced law transports to equality
of the actual spatial representatives under the physical project map. -/
theorem ae_akmUnscaledCoefficientFactor_project {d : ℕ} {L r₀ : ℝ} {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩)
    (G : FieldPair d → E) (hG : Measurable G)
    (F : CoefficientField d → E) (hF : Measurable F)
    (hGF : G =ᵐ[reducedEnvironmentLaw Q] fun ω => F ω.1) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate x (reduce ω.1)) = akmUnscaledCoefficientFactor r₀ R F
        (project (r₀ := r₀) Q.ellipticity_parameter ω) x := by
  have hprod : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      G (translate x ω) = F (translate x ω).1 :=
    ae_of_all _ fun x => (measurePreserving_translate _
      (reducedEnvironmentLaw_stationary Q) x).quasiMeasurePreserving.ae hGF
  have hswap : ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate x ω) = F (translate x ω).1 := by
    apply (Measure.ae_ae_comm ?_).mp hprod
    exact measurableSet_eq_fun (hG.comp Probability.continuous_translate.measurable)
      (hF.comp (continuous_fst.comp Probability.continuous_translate).measurable)
  have hp : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate x (reduce ω.1)) = F (translate x (reduce ω.1)).1 := by
    have h := ae_of_ae_map Probability.measurable_reduce.aemeasurable hswap
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [hp] with ω hω
  have hfst (x : Vec d) :
      (translate x (reduce ω.1)).1 =
        (translate x ((reduce ω.1).1, (0 : C(Vec d, ℝ)))).1 := rfl
  simpa only [akmUnscaledCoefficientFactor,
    akmReducedReconstruction_project Q.ellipticity_parameter
      (lt_of_lt_of_le zero_lt_one Q.range_parameter).ne' R hReq, hfst] using hω

end EinsteinRelation.Correctors
