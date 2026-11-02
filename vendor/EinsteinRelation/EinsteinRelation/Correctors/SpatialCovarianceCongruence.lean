import EinsteinRelation.Correctors.AKMCarrierIdentificationCovariance

/-!
# Covariance under replacement of spatial representatives

Source: `paper/main.tex:693-702`. Invariance of the coefficient law and
of spatial volume transports each of the two null sets in a covariance
identity. No pointwise representative or uniqueness premise is needed.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- Spatial covariance passes between representatives equal almost surely
in the parameter and almost everywhere in space. -/
theorem ae_spatial_covariance_congr {d : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (τ : A → A) (hτ : MeasurePreserving τ P P) (z : Vec d)
    (f g : A → Vec d → Vec d)
    (heq : ∀ᵐ a ∂P, (fun x => f a x) =ᵐ[volume] (fun x => g a x))
    (hcov : ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      g a (x + z) = g (τ a) x) :
    ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), f a (x + z) = f (τ a) x := by
  filter_upwards [heq, hτ.quasiMeasurePreserving.ae heq, hcov] with a ha hτa hca
  have hshift := (measurePreserving_add_right (volume : Measure (Vec d)) z).quasiMeasurePreserving.ae ha
  filter_upwards [hshift, hτa, hca] with x hx hy hz
  exact hx.trans (hz.trans hy.symm)

end EinsteinRelation.Correctors
