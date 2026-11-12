import EinsteinRelation.Correctors.AKMStationarityFromIdentification

/-!
# Real translations on the actual coefficient law

Source: `paper/main.tex:724-731`. Translating the environment backwards
and the spatial argument forwards leaves the canonical gradient unchanged
almost surely. This is the gradient identity needed to transport the planar
origin-ball estimates to arbitrary centers.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

private theorem coefficient_eq_of_field_eq {d : ℕ} {K : ℝ}
    (a b : Coefficient d K) (h : a.field = b.field) : a = b := by
  cases a with
  | mk f hi hs he =>
    cases b with
    | mk g hi' hs' he' =>
      change f = g at h
      subst g
      rfl

/-- Coefficient translations form an additive action on the actual carrier. -/
theorem translateCoefficient_add {d : ℕ} {K : ℝ}
    (z w : Vec d) (a : Coefficient d K) :
    translateCoefficient z (translateCoefficient w a) = translateCoefficient (z + w) a := by
  have heq : (translateCoefficient z (translateCoefficient w a)).field =
      (translateCoefficient (z + w) a).field := by
    funext x
    change a (w + (z + x)) = a ((z + w) + x)
    congr 1
    abel
  exact coefficient_eq_of_field_eq _ _ heq

/-- The zero translation fixes each coefficient field. -/
theorem translateCoefficient_zero {d : ℕ} {K : ℝ} (a : Coefficient d K) :
    translateCoefficient 0 a = a := by
  have heq : (translateCoefficient 0 a).field = a.field := by
    funext x
    simp [translateCoefficient]
  exact coefficient_eq_of_field_eq _ _ heq

/-- The actual law is measure preserving under every real spatial translation. -/
theorem measurePreserving_actualCoefficientTranslation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (z : Vec d) :
    MeasurePreserving (translateCoefficient z) (actualCoefficientLaw Q)
      (actualCoefficientLaw Q) :=
  ⟨measurable_translateCoefficient z, actualCoefficientLaw_translation_invariant_real Q z⟩

/-- Translation is a measurable equivalence for the test-integral sigma algebra. -/
noncomputable def coefficientTranslationEquiv {d : ℕ} {K : ℝ} (z : Vec d) :
    Coefficient d K ≃ᵐ Coefficient d K where
  toFun := translateCoefficient z
  invFun := translateCoefficient (-z)
  left_inv a := by rw [translateCoefficient_add, neg_add_cancel, translateCoefficient_zero]
  right_inv a := by rw [translateCoefficient_add, add_neg_cancel, translateCoefficient_zero]
  measurable_toFun := measurable_translateCoefficient z
  measurable_invFun := measurable_translateCoefficient (-z)

/-- Real translation preserves every lower integral, including the moment
functionals of potentials without a joint measurability hypothesis. -/
theorem lintegral_actualCoefficientTranslation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (z : Vec d)
    (f : Coefficient d (AKMUpperEllipticity L) → ENNReal) :
    (∫⁻ a, f (translateCoefficient z a) ∂actualCoefficientLaw Q) =
      ∫⁻ a, f a ∂actualCoefficientLaw Q :=
  (measurePreserving_actualCoefficientTranslation Q z).lintegral_comp_emb
    (coefficientTranslationEquiv z).measurableEmbedding f

/-- Backwards environment translation cancels forwards spatial translation
for any jointly measurable gradient identified with the canonical one. -/
theorem ae_inverse_translated_canonicalAKMGradient
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (z : Vec d) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      φ.grad (translateCoefficient (-z) a) (x + z) = φ.grad a x := by
  have h := (measurePreserving_actualCoefficientTranslation Q (-z)).quasiMeasurePreserving.ae
    (ae_akm_stationary_of_canonical_gradient Q i φ.grad φ.measurable_grad hid z)
  simpa only [translateCoefficient_add, add_neg_cancel, translateCoefficient_zero] using h

end EinsteinRelation.Correctors
