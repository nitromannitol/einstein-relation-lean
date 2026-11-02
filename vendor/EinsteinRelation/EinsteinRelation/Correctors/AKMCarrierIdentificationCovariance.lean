import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport
import EinsteinRelation.Calculus.SpatialEqualityPushforward

/-!
# Covariance of the reconstructed AKM gradient

Source: `paper/main.tex:693-702`. The constructed gradient intertwines
translations on every coefficient in the physical project image, before
any null-set argument. The normalization of space remains explicit.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- On the project image the reconstructed gradient is spatially covariant
pointwise, even though its coefficient factor is merely measurable. -/
theorem akmGradientFromCoefficientFactor_project_covariance
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩)
    (F : CoefficientField d → EuclideanSpace ℝ (Fin d))
    (ω : PhysicalField d L) (x z : Vec d) :
    akmGradientFromCoefficientFactor (d := d) (L := L) r₀ R F
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (x + z) =
      akmGradientFromCoefficientFactor (d := d) (L := L) r₀ R F
        (translateCoefficient z (project (r₀ := r₀) Q.ellipticity_parameter ω)) x := by
  have hr : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
  rw [project_translation_covariant]
  unfold akmGradientFromCoefficientFactor
  rw [akmReducedReconstruction_project Q.ellipticity_parameter hr R hReq ω,
    akmReducedReconstruction_project Q.ellipticity_parameter hr R hReq
      (physicalTranslate (r₀ • z) ω)]
  have ht : reduce (physicalTranslate (r₀ • z) ω).1 =
      translate (r₀ • z) (reduce ω.1) := reduce_translate ω.1 (r₀ • z)
  rw [ht]
  have hc : (translate (r₀ • (x + z)) ((reduce ω.1).1, 0)).1 =
      (translate (r₀ • x) ((translate (r₀ • z) (reduce ω.1)).1, 0)).1 := by
    ext y i j
    change (reduce ω.1).1 (r₀ • (x + z) + y) i j =
      (reduce ω.1).1 (r₀ • z + (r₀ • x + y)) i j
    rw [smul_add, add_assoc, add_left_comm (r₀ • x) (r₀ • z)]
  rw [hc]

/-- Jointly measurable covariance on the actual project image transfers
through the raw coefficient law. -/
theorem ae_akm_covariance_of_project_covariance
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2))
    (z : Vec d)
    (hcov : ∀ (ω : PhysicalField d L) x,
      g (project (r₀ := r₀) Q.ellipticity_parameter ω) (x + z) =
        g (translateCoefficient z (project (r₀ := r₀) Q.ellipticity_parameter ω)) x) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      g a (x + z) = g (translateCoefficient z a) x := by
  have hl : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      g p.1 (p.2 + z)) :=
    hg.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
  have hr : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      g (translateCoefficient z p.1) p.2) :=
    hg.comp (((measurable_translateCoefficient z).comp measurable_fst).prodMk measurable_snd)
  exact ae_spatial_eq_of_map_pullback (physicalReferenceLaw Q) volume
    (project (r₀ := r₀) Q.ellipticity_parameter) (measurable_project Q.ellipticity_parameter)
    (fun a x => g a (x + z)) (fun a x => g (translateCoefficient z a) x)
    hl hr (ae_of_all _ fun ω => ae_of_all _ fun x => hcov ω x)

/-- The actual raw coefficient law carries the full real spatial covariance
of the reconstructed canonical gradient, including lattice stationarity. -/
theorem ae_akmGradientFromCoefficientFactor_covariance
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩)
    (F : CoefficientField d → EuclideanSpace ℝ (Fin d)) (hF : StronglyMeasurable F)
    (z : Vec d) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      akmGradientFromCoefficientFactor (d := d) (L := L) r₀ R F a (x + z) =
        akmGradientFromCoefficientFactor (d := d) (L := L) r₀ R F (translateCoefficient z a) x := by
  exact ae_akm_covariance_of_project_covariance Q
    (akmGradientFromCoefficientFactor (d := d) (L := L) r₀ R F)
    (measurable_akmGradientFromCoefficientFactor (d := d) (L := L) r₀ R hR F hF) z
    (fun ω x => akmGradientFromCoefficientFactor_project_covariance Q R hReq F ω x z)

end EinsteinRelation.Correctors
