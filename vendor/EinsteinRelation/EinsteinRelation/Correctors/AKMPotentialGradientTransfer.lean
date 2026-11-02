import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport
import EinsteinRelation.Correctors.SpatialWeakDilation
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-!
# The gradient of the rescaled AKM scalar potential

Source: `paper/main.tex:693-702,716`. The scalar potential has the physical
normalization `2 r₀ φ(x/r₀)` because the raw corrector direction is `eᵢ/2`.
The conclusion identifies the weak gradient everywhere in space, up to null
sets, without an assumed potential-identification or uniqueness statement.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- A global affine-gradient identification gives the actual weak gradient
of the rescaled potential on the physical coefficient law. -/
theorem ae_akmPotential_has_canonical_weakGradient
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      HasWeakGradient Set.univ
        (fun x => (2 * r₀) * φ.potential
          (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x))
        (fun x => ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Fact.out : 2 ≤ d)
  have hw := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae φ.weak_gradient
  have hl := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae
    φ.locally_square_integrable
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [hw, hl, hid] with ω hω hlω hiω
  have hscaled := hasWeakGradient_dilation _ _
    (fun R hR => (hlω R hR).1) (fun R hR => (hlω R hR).2) hω
    r₀⁻¹ (2 * r₀) (inv_pos.mpr hr)
  have hi := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec (2 + k)))
    (inv_ne_zero hr.ne')).ae hiω
  have heq : (fun x => ((2 * r₀) * r₀⁻¹) • φ.grad
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) =ᵐ[volume]
      (fun x => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin (2 + k))) 2 (reducedEnvironmentLaw Q))
          (translate x (reduce ω.1))).ofLp) := by
    filter_upwards [hi] with x hx
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hx
    have hfactor : (2 * r₀) * r₀⁻¹ = (2 : ℝ) := by
      rw [mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]
    rw [hfactor]
    ext j
    have hj := congrFun hx j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, PiLp.add_apply,
      halfDirection, correctorUnitVector, unitVector,
      Pi.single_apply] at hj ⊢
    split_ifs at hj ⊢ <;> linarith only [hj]
  intro j
  apply (hscaled j).congr_ae (ae_eq_refl _)
  rw [Measure.restrict_univ]
  exact heq.mono fun x hx => congrFun hx j

end EinsteinRelation.Correctors
