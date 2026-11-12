import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport

/-!
# Observational identification of reconstructed AKM coefficients

Source: `paper/main.tex:699-708`, AKM (0.11). Smooth observations of the
raw coefficient and its continuous reconstruction agree almost surely.
A countable determining family turns those measurable equalities into
spatial almost-everywhere equality. Continuity of arbitrary raw fields
is never asserted to be a measurable event.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- A reconstruction agreeing with continuous raw coefficients agrees
pointwise with the actual normalized project image. -/
theorem akmContinuousReconstruction_project {d : ℕ} {L r₀ : ℝ}
    (hL : 1 ≤ L)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩) (ω : PhysicalField d L) :
    R (project (r₀ := r₀) hL ω) =
      rescaleCoefficientField (ellipticityScale L) r₀ (reduce ω.1).1 := by
  have hc : Continuous (project (r₀ := r₀) hL ω).field := by
    change Continuous (fun x => ellipticityScale L • reducedCoefficient ω.1 (r₀ • x))
    exact (continuous_const.smul
      ((Real.continuous_exp.comp (continuous_const.mul ω.1.2.continuous)).smul
        ω.1.1.continuous)).comp (continuous_const.smul continuous_id)
  rw [hReq _ hc]
  rfl

/-- Each smooth observation agrees on one measurable full-law event. -/
theorem ae_akm_reconstruction_testIntegral_eq {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩) (u : SmoothCompactTest d) (i j : Fin d) :
    ∀ᵐ a ∂actualCoefficientLaw Q,
      testIntegral a u i j = ∫ x, u x * R a x i j := by
  have hA : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => R p.1 p.2) :=
    continuous_eval.measurable.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hf : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      u p.2 * R p.1 p.2 i j) :=
    (u.smooth.continuous.measurable.comp measurable_snd).mul
      (((show Continuous (fun A : Mat d => A i j) from
        (continuous_apply j).comp (continuous_apply i)).measurable).comp hA)
  apply (ae_map_iff (measurable_project Q.ellipticity_parameter).aemeasurable
    (measurableSet_eq_fun (measurable_testIntegral u i j)
      hf.stronglyMeasurable.integral_prod_right.measurable)).mpr
  exact ae_of_all _ fun ω => by
    rw [akmContinuousReconstruction_project Q.ellipticity_parameter R hReq ω]
    rfl

/-- Countably many determining observations identify the actual raw field
with its continuous reconstruction, up to spatial null sets. The only
extra premise is the stated deterministic determining-test property. -/
theorem ae_akm_field_eq_reconstruction_of_determining_tests
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩)
    (T : ℕ → SmoothCompactTest d)
    (hT : ∀ f g : Vec d → ℝ,
      LocallyIntegrable f volume → LocallyIntegrable g volume →
      (∀ n, (∫ x, T n x * f x) = ∫ x, T n x * g x) → f =ᵐ[volume] g) :
    ∀ᵐ a ∂actualCoefficientLaw Q, a.field =ᵐ[volume] (R a : Vec d → Mat d) := by
  have ht := ae_all_iff.mpr fun n => ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    ae_akm_reconstruction_testIntegral_eq Q R hR hReq (T n) i j
  filter_upwards [ht] with a ha
  have hc (i j : Fin d) : (fun x => a x i j) =ᵐ[volume] (fun x => R a x i j) := by
    apply hT _ _ (a.locally_integrable i j)
      (((continuous_apply j).comp ((continuous_apply i).comp (R a).continuous)).locallyIntegrable)
    exact fun n => ha n i j
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hc i)] with x hx
  exact funext fun i => funext fun j => hx i j

end EinsteinRelation.Correctors
