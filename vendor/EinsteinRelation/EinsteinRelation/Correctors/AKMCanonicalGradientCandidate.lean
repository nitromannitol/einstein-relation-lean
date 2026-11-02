import EinsteinRelation.Correctors.CanonicalCoefficientMeasurability
import EinsteinRelation.Correctors.AKMEnergyTransfer
import EinsteinRelation.Environment.AKMContinuousReconstruction
import EinsteinRelation.Environment.CoefficientFieldRescaling

/-!
# A canonical gradient representative on the AKM coefficient carrier

Source: `paper/main.tex:693-702,727-729`. Recover the normalized continuous
coefficient, undo its normalization and dilation, and evaluate the
coefficient-only canonical gradient along spatial translations. This file
constructs a measurable gradient representative, not an AKM corrector.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- Undo the AKM normalization in a reconstructed continuous coefficient. -/
def akmReducedReconstruction {d : ℕ} {L : ℝ} (r₀ : ℝ)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (a : Coefficient d (AKMUpperEllipticity L)) : CoefficientField d :=
  rescaleCoefficientField (ellipticityScale L)⁻¹ r₀⁻¹ (R a)

/-- The rescaled coefficient-only spatial gradient on the raw AKM carrier. -/
def akmGradientFromCoefficientFactor {d : ℕ} {L : ℝ} (r₀ : ℝ)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (F : CoefficientField d → EuclideanSpace ℝ (Fin d))
    (a : Coefficient d (AKMUpperEllipticity L)) (y : Vec d) : Vec d :=
  (1 / 2 : ℝ) • (F (translate (r₀ • y) (akmReducedReconstruction r₀ R a, 0)).1).ofLp

/-- The candidate gradient is jointly measurable in raw coefficients and space. -/
theorem measurable_akmGradientFromCoefficientFactor {d : ℕ} {L : ℝ} (r₀ : ℝ)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (F : CoefficientField d → EuclideanSpace ℝ (Fin d)) (hF : StronglyMeasurable F) :
    Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      akmGradientFromCoefficientFactor r₀ R F p.1 p.2) := by
  letI : MeasurableSpace C(Vec d, ℝ) := borel _
  letI : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
  have hrec : Measurable (akmReducedReconstruction r₀ R) :=
    (measurable_rescaleCoefficientField d _ _).comp hR
  have hfieldPair : Measurable (fun a =>
      (akmReducedReconstruction r₀ R a, (0 : C(Vec d, ℝ))) :
      Coefficient d (AKMUpperEllipticity L) → FieldPair d) := by
    change @Measurable _ (CoefficientField d × C(Vec d, ℝ)) _ (borel _) _
    rw [← (Prod.borelSpace (α := CoefficientField d) (β := C(Vec d, ℝ))).measurable_eq]
    exact hrec.prodMk measurable_const
  have hpair : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      (r₀ • p.2, (akmReducedReconstruction r₀ R p.1, (0 : C(Vec d, ℝ))))) :=
    (measurable_snd.const_smul r₀).prodMk
      (hfieldPair.comp measurable_fst)
  have htrans := Probability.continuous_translate.measurable.comp hpair
  exact Measurable.const_smul
    ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      (hF.measurable.comp ((continuous_fst.comp Probability.continuous_translate).measurable.comp hpair))) (1 / 2 : ℝ)

/-- Reconstruction cancels the literal coefficient normalization of the
physical project map pointwise, without a law or null-set argument. -/
theorem akmReducedReconstruction_project {d : ℕ} {L r₀ : ℝ}
    (hL : 1 ≤ L) (hr₀ : r₀ ≠ 0)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hR : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩) (ω : PhysicalField d L) :
    akmReducedReconstruction r₀ R (project (r₀ := r₀) hL ω) = (reduce ω.1).1 := by
  have hc : Continuous (project (r₀ := r₀) hL ω).field := by
    change Continuous (fun x => ellipticityScale L • reducedCoefficient ω.1 (r₀ • x))
    exact (((Real.continuous_exp.comp (continuous_const.mul ω.1.2.continuous)).smul
        ω.1.1.continuous).const_smul (ellipticityScale L)).comp (continuous_id.const_smul r₀)
  unfold akmReducedReconstruction
  rw [hR _ hc]
  ext x i j
  change ((ellipticityScale L)⁻¹ •
    (ellipticityScale L • reducedCoefficient ω.1 (r₀ • (r₀⁻¹ • x)))) i j = _
  simp only [smul_smul, mul_inv_cancel₀ hr₀, one_smul,
    inv_mul_cancel₀ (ellipticityScale_pos hL).ne']
  rfl

/-- A jointly measurable gradient candidate on the literal AKM carrier
has the exact canonical gradient identification under the actual law. No
corrector properties are bundled into this existence statement. -/
theorem exists_measurable_akm_canonical_gradient {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d,
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i +
          g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp := by
  obtain ⟨R, hR, hReq⟩ := exists_measurable_continuous_reconstruction
    (d := d) (K := AKMUpperEllipticity L)
  obtain ⟨F, hF, hFG⟩ := exists_coefficient_factor_of_canonicalGradient Q i
  refine ⟨akmGradientFromCoefficientFactor r₀ R F,
    measurable_akmGradientFromCoefficientFactor r₀ R hR F hF, ?_⟩
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  have hprod : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      G (translate x ω) = F (translate x ω).1 :=
    ae_of_all _ fun x =>
      (measurePreserving_translate _ (reducedEnvironmentLaw_stationary Q) x).quasiMeasurePreserving.ae hFG
  have hswap : ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate x ω) = F (translate x ω).1 := by
    apply (Measure.ae_ae_comm ?_).mp hprod
    exact measurableSet_eq_fun
      ((Lp.stronglyMeasurable G).measurable.comp Probability.continuous_translate.measurable)
      (hF.measurable.comp (continuous_fst.comp Probability.continuous_translate).measurable)
  have hp : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate x (reduce ω.1)) = F (translate x (reduce ω.1)).1 := by
    have h := ae_of_ae_map Probability.measurable_reduce.aemeasurable hswap
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  have hr : r₀ ≠ 0 := (lt_of_lt_of_le zero_lt_one Q.range_parameter).ne'
  filter_upwards [hp] with ω hω
  have hy := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr).ae hω
  filter_upwards [hy] with y hy
  unfold akmGradientFromCoefficientFactor
  rw [akmReducedReconstruction_project Q.ellipticity_parameter hr R hReq ω]
  have hc : (translate (r₀ • y) ((reduce ω.1).1, (0 : C(Vec d, ℝ)))).1 =
      (translate (r₀ • y) (reduce ω.1)).1 := rfl
  rw [hc, ← hy]
  ext j
  by_cases hj : j = i <;> simp [halfDirection, correctorUnitVector, unitVector,
    PiLp.add_apply, hj, G]
  all_goals ring

end EinsteinRelation.Correctors
