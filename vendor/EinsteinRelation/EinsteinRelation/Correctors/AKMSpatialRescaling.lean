import EinsteinRelation.Correctors.AKMEnergyTransfer
import EinsteinRelation.Correctors.InteriorGradientTransfer
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The spatial rescaling identity for the AKM corrector

Source: `paper/main.tex:727-729`. Once the source gradient is identified
with the rescaled canonical spatial gradient, all factors of `r₀`, the
half direction, and the unit-ball normalization are computed here.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

private theorem measurableSet_ball {d : ℕ} (ρ : ℝ) : MeasurableSet (ball (0 : Vec d) ρ) := by
  unfold ball euclideanNorm euclideanSq dot
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- Change of variables from a physical unit ball to a normalized ball of
radius `r⁻¹`. Both domains and the Jacobian use Euclidean dimension `d`. -/
theorem integral_unitBall_inv_smul {d : ℕ} (f : Vec d → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x in ball 0 1, f (r⁻¹ • x) ∂volume) =
      r ^ d * ∫ y in ball 0 r⁻¹, f y ∂volume := by
  have hpre (x : Vec d) : r⁻¹ • x ∈ ball 0 r⁻¹ ↔ x ∈ ball 0 1 := by
    simp only [ball, Set.mem_setOf_eq, sub_zero, euclideanNorm_smul _ (inv_nonneg.mpr hr.le)]
    simpa only [mul_one] using
      (mul_lt_mul_iff_right₀ (a := r⁻¹) (b := euclideanNorm x) (c := 1) (inv_pos.mpr hr))
  have hind : (fun x : Vec d => (ball (0 : Vec d) r⁻¹).indicator f (r⁻¹ • x)) =
      (ball (0 : Vec d) 1).indicator (fun x => f (r⁻¹ • x)) := by
    funext x
    by_cases hx : x ∈ ball (0 : Vec d) 1
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hpre x).mpr hx)]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hpre x).mp hx)]
  have h := Measure.integral_comp_inv_smul_of_nonneg volume
    ((ball (0 : Vec d) r⁻¹).indicator f) hr.le
  rw [hind, integral_indicator (measurableSet_ball 1),
    integral_indicator (measurableSet_ball r⁻¹)] at h
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul] using h

/-- The local-energy rescaling follows from a literal a.e. spatial
gradient identity, without a stochastic estimate or a PDE regularity input. -/
theorem unitEnergyRescaling_identity_of_gradient {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (ω : FieldPair d) (v : Vec d → Vec d)
    (hv : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
      (2 : ℝ) • v (r₀⁻¹ • x) = (correctorUnitVector i +
        (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) :
    canonicalCorrectorUnitEnergy Q i ω ^ 2 = unitEnergyRescaling d r₀ *
      (∫ y in ball 0 r₀⁻¹, euclideanSq (v y) ∂volume) := by
  have hr : 0 < r₀ := lt_of_lt_of_le zero_lt_one Q.range_parameter
  have hroot := canonicalUnitEnergy_eq_of_gradient_ae Q i ω (fun x => 2 • v (r₀⁻¹ • x)) hv
  have hsqnonneg (x : Vec d) : 0 ≤ euclideanSq ((2 : ℝ) • v (r₀⁻¹ • x)) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hnonneg : 0 ≤ ⨍ x in ball (0 : Vec d) 1,
      euclideanSq ((2 : ℝ) • v (r₀⁻¹ • x)) ∂volume := by
    rw [average_eq]
    exact smul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hsqnonneg)
  rw [← hroot, Real.sq_sqrt hnonneg]
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  simp_rw [euclideanSq_smul]
  rw [integral_const_mul, integral_unitBall_inv_smul (fun y => euclideanSq (v y)) hr]
  have hvolume : volume (ball (0 : Vec d) 1) =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    have hpre : (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' ball 0 1 =
        Metric.ball 0 1 := by
      ext x
      have hn : euclideanNorm x.ofLp = ‖x‖ := by
        rw [EuclideanSpace.norm_eq]
        unfold euclideanNorm euclideanSq dot
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Real.norm_eq_abs, pow_two]
        exact (abs_mul_abs_self (x j)).symm
      simp only [Set.mem_preimage, ball, Set.mem_setOf_eq, sub_zero, Metric.mem_ball,
        dist_zero_right, hn]
    rw [← hpre]
    exact ((PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (measurableSet_ball 1).nullMeasurableSet).symm
  rw [hvolume]
  unfold unitEnergyRescaling
  ring

/-- The remaining source-to-canonical identification, without an assumed
local-energy estimate or rescaling identity. The source spatial corrector
and the canonical horizontal gradient must be shown to represent the same
gradient; the latter's existing variational uniqueness theorem is available.
The source flux identity and Gaussian integrability also remain internal. -/
structure CanonicalAKMSpatialRealization {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) where
  corrector : Corrector (actualCoefficientLaw Q) (halfDirection i)
  gradient_identification : ∀ᵐ ω ∂physicalReferenceLaw Q,
    ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
      (2 : ℝ) • (halfDirection i +
        corrector.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate x (reduce ω.1))).ofLp
  mean_flux_identity : dot (halfDirection i) (meanFlux corrector) =
    ellipticityScale L / 4 * dot (unitVector i) ((homogenizedMatrix Q).mulVec (unitVector i))
  heat_integrable : ∀ᵐ a ∂actualCoefficientLaw Q,
    Integrable (fun y => heatKernel 0 1 y * ((1 / 2 : ℝ) *
      dot (halfDirection i + corrector.grad a y)
        ((a y).mulVec (halfDirection i + corrector.grad a y)))) volume

/-- Discharge the spatial Jacobian and energy normalization fields of the
energy-transfer interface from the gradient identification alone. -/
def CanonicalAKMSpatialRealization.toEnergyRealization {d : ℕ} {L r₀ : ℝ}
    {Q : EnvironmentLaw d L r₀} {i : Fin d} (R : CanonicalAKMSpatialRealization Q i) :
    CanonicalAKMRealization Q i where
  corrector := R.corrector
  local_energy_identity := R.gradient_identification.mono fun ω hω =>
    unitEnergyRescaling_identity_of_gradient Q i (reduce ω.1)
      (fun y => halfDirection i + R.corrector.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y)
      hω
  mean_flux_identity := R.mean_flux_identity
  heat_integrable := R.heat_integrable

end EinsteinRelation.Correctors

