import EinsteinRelation.Correctors.AKMRealTranslation
import EinsteinRelation.Correctors.SpatialWeakTranslation
import EinsteinRelation.Correctors.ScalarGaugeReconstruction

/-!
# Translating an actual scalar corrector

Source: `paper/main.tex:724-731`. A backwards environment translation
and a forwards spatial translation preserve the canonical gradient.
The new potential therefore inherits centered sublinearity from the old
one by the proved constant-gauge theorem.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The shifted scalar potential is a weak potential of the original gradient. -/
theorem ae_inverse_translated_scalar_weakGradient
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (z : Vec d) :
    ∀ᵐ a ∂actualCoefficientLaw Q,
      HasWeakGradient Set.univ
        (fun x => φ.potential (translateCoefficient (-z) a) (x + z)) (φ.grad a) := by
  have hw := (measurePreserving_actualCoefficientTranslation Q (-z)).quasiMeasurePreserving.ae
    φ.weak_gradient
  filter_upwards [hw, ae_inverse_translated_canonicalAKMGradient Q i φ hid z] with a ha hc
  have ht := hasWeakGradient_translation _ _ ha z
  intro l
  apply (ht l).congr_ae (ae_eq_refl _)
  simpa only [Measure.restrict_univ] using
    (hc.mono fun x hx => congrArg (fun v : Vec d => v l) hx)

/-- Recenter the actual scalar corrector while retaining its canonical gradient. -/
noncomputable def inverseTranslatedScalarCorrector
    {d : ℕ} (hd : 0 < d) {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (z : Vec d) : Corrector (actualCoefficientLaw Q) (halfDirection i) :=
  correctorWithPotential hd φ
    (fun a x => φ.potential (translateCoefficient (-z) a) (x + z))
    (ae_inverse_translated_scalar_weakGradient Q i φ hid z)

end EinsteinRelation.Correctors
