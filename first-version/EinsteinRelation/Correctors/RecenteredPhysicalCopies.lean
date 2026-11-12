import EinsteinRelation.Correctors.ConditionalCopyRecentering
import EinsteinRelation.Correctors.PhysicalCouplingLift
import EinsteinRelation.Correctors.AKMPhysicalPotentials

/-! # Physical lifts of the actual recentered copies

Source: `paper/main.tex:817–875,886–894`. Pullback along the injective
physical reduction retains the actual copy law. The normalized coefficients
agree on the correctly dilated ball. Canonical spatial energies are identified
from the full-space AKM gradient identity, with no fixed-point evaluation.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM ReductionImageV3 Environment.AKMTestIntegralSupport
open NormalizedSpatialRepresentativeSupport

/-- The physical lift of the actual recentered conditional-copy law.
Source: `paper/main.tex:817–875,886–894`. -/
noncomputable def recenteredPhysicalCopyLaw {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (y : Point d) :
    Measure (PhysicalField d L × PhysicalField d L) :=
  physicalCouplingLift (recenteredConditionalCopyLaw Q R y)

/-- Both actual physical marginals, the exact reduction pushforward, and
agreement of the normalized coefficients on the ball of radius `8R/r₀`.
Source: `paper/main.tex:817–875,886–894`. -/
theorem recenteredPhysicalCopy_properties {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (y : Point d) :
    IsProbabilityMeasure (recenteredPhysicalCopyLaw Q R y) ∧
      MeasurePreserving physicalPairReduction (recenteredPhysicalCopyLaw Q R y)
        (recenteredConditionalCopyLaw Q R y) ∧
      MeasurePreserving Prod.fst (recenteredPhysicalCopyLaw Q R y) (physicalReferenceLaw Q) ∧
      MeasurePreserving Prod.snd (recenteredPhysicalCopyLaw Q R y) (physicalReferenceLaw Q) ∧
      ∀ᵐ z ∂recenteredPhysicalCopyLaw Q R y,
        Set.EqOn (project (r₀ := r₀) Q.ellipticity_parameter z.1)
          (project (r₀ := r₀) Q.ellipticity_parameter z.2) (originBall d (8*R/r₀)) := by
  obtain ⟨hν, hfst, hsnd, heq⟩ := recenteredConditionalCopy_properties Q R y
  letI : IsProbabilityMeasure (recenteredConditionalCopyLaw Q R y) := hν
  obtain ⟨hμ, hred, h₁, h₂⟩ := physicalCouplingLift_properties Q _ hfst hsnd
  refine ⟨hμ, hred, h₁, h₂, ?_⟩
  filter_upwards [hred.quasiMeasurePreserving.ae heq] with z hz
  intro x hx
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hmem : r₀ • x ∈ originBall d (8*R) := by
    change euclideanNorm (r₀ • x) < 8*R
    rw [euclideanNorm_smul _ hr.le]
    change euclideanNorm x < 8*R/r₀ at hx
    simpa only [mul_comm] using (lt_div_iff₀ hr).mp hx
  have he := hz hmem
  exact congrArg (fun M : Mat d => ellipticityScale L • M) he

/-- The spatial energy of the actual canonical gradient difference is
exactly that of the identified AKM gradient in physical coordinates.
The identity is valid for every spatial averaging set, independently of
pointwise versions. Source: `paper/main.tex:834–861`. -/
theorem ae_recenteredPhysicalCopy_gradient_energy_identification
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : CanonicalAKMGradientIdentification Q i φ)
    (R : ℝ) (y : Point d) (V : Set (Vec d)) :
    (fun z : PhysicalField d L × PhysicalField d L => vectorRms volume V (fun x =>
      conditionalCorrectorGradient Q i (WithLp.toLp 2 x) (reduce z.1.1) -
        conditionalCorrectorGradient Q i (WithLp.toLp 2 x) (reduce z.2.1)))
      =ᵐ[recenteredPhysicalCopyLaw Q R y]
    (fun z => vectorRms volume V (fun x => (2 : ℝ) •
      (φ.grad (project (r₀ := r₀) Q.ellipticity_parameter z.1) (r₀⁻¹ • x) -
        φ.grad (project (r₀ := r₀) Q.ellipticity_parameter z.2) (r₀⁻¹ • x)))) := by
  obtain ⟨_, _, hfst, hsnd, _⟩ := recenteredPhysicalCopy_properties Q R y
  have hr₀ : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
  have hr : r₀⁻¹ ≠ 0 := inv_ne_zero hr₀
  filter_upwards [hfst.quasiMeasurePreserving.ae hid,
    hsnd.quasiMeasurePreserving.ae hid] with z h₁ h₂
  have h₁' := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr).ae h₁
  have h₂' := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr).ae h₂
  have heq : (fun x => conditionalCorrectorGradient Q i (WithLp.toLp 2 x) (reduce z.1.1) -
      conditionalCorrectorGradient Q i (WithLp.toLp 2 x) (reduce z.2.1)) =ᵐ[volume]
      fun x => (2 : ℝ) •
        (φ.grad (project (r₀ := r₀) Q.ellipticity_parameter z.1) (r₀⁻¹ • x) -
          φ.grad (project (r₀ := r₀) Q.ellipticity_parameter z.2) (r₀⁻¹ • x)) := by
    filter_upwards [h₁', h₂'] with x hx₁ hx₂
    simp only [smul_smul, mul_inv_cancel₀ hr₀, one_smul] at hx₁ hx₂
    ext j
    have h₁j := congrFun hx₁ j
    have h₂j := congrFun hx₂ j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, PiLp.add_apply,
      conditionalCorrectorGradient, StationarySpatialRealization.spatialRealization,
      Pi.sub_apply] at h₁j h₂j ⊢
    linarith
  unfold vectorRms
  congr 1
  rw [setAverage_eq, setAverage_eq]
  congr 1
  exact integral_congr_ae ((ae_restrict_of_ae heq).mono fun x hx => congrArg euclideanSq hx)

end EinsteinRelation.Correctors
