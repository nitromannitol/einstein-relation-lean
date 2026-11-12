import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # The local flux error rate

Source: `paper/main.tex:942–949,969–977`. The literal local flux error
`a(0) H - K` inherits the inverse radius bound using the almost sure
ellipticity of the actual reduced environment law and Euclidean norms.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Local flux error in `L^p` under the reduced law. The origin coefficient is elliptic with
constant `exp (2 L) * L` almost surely, so the Euclidean triangle inequality and the scaled
`L^p` bounds give the stated rate. Source: `paper/main.tex:942–949,969–977`. -/
theorem eLpNorm_local_flux_error_rate_le {d : ℕ} {L r0 p R B D : ℝ}
    (Q : EnvironmentLaw d L r0) (hp : 1 ≤ p) (hR : 1 ≤ R) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {H K : FieldPair d → Vec d} (hHm : Measurable H) (hKm : Measurable K)
    (hH : eLpNorm (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q)
      ≤ ENNReal.ofReal (B * R⁻¹))
    (hK : eLpNorm (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q)
      ≤ ENNReal.ofReal (D * R⁻¹)) :
    eLpNorm (fun ω => euclideanNorm ((ω.1 (0 : Vec d)).mulVec (H ω) - K ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q)
      ≤ ENNReal.ofReal (((Real.exp (2 * L) * L) * B + D) * R⁻¹) := by
  have hL1 : 1 ≤ L := Q.ellipticity_parameter
  have hLpos : 0 < Real.exp (2 * L) * L := mul_pos (Real.exp_pos _) (by linarith)
  have hΛnn : 0 ≤ Real.exp (2 * L) * L := hLpos.le
  have hRpos : 0 < R := by linarith
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  -- Euclidean coordinate map: the norm is the Euclidean one, not the sup norm.
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hNJ : ∀ v : Vec d, euclideanNorm v = ‖J v‖ := fun v =>
    TimeChange.euclideanNorm_eq_norm_toLp v
  have hN0 : ∀ v : Vec d, 0 ≤ euclideanNorm v := fun v => by
    rw [hNJ v]
    exact norm_nonneg _
  have htri : ∀ u v : Vec d, euclideanNorm (u - v) ≤ euclideanNorm u + euclideanNorm v := by
    intro u v
    rw [hNJ, hNJ, hNJ, map_sub]
    exact norm_sub_le _ _
  have hNcont : Continuous (fun v : Vec d => euclideanNorm v) :=
    (continuous_norm.comp J.continuous).congr fun v => (hNJ v).symm
  have hHN : Measurable (fun ω => euclideanNorm (H ω)) := hNcont.measurable.comp hHm
  have hKN : Measurable (fun ω => euclideanNorm (K ω)) := hNcont.measurable.comp hKm
  -- a.e. origin ellipticity of the actual coefficient under the reduced law
  have hpt : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      euclideanNorm ((ω.1 (0 : Vec d)).mulVec (H ω) - K ω)
        ≤ Real.exp (2 * L) * L * euclideanNorm (H ω) + euclideanNorm (K ω) := by
    filter_upwards [ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hω
    have h1 : euclideanNorm ((ω.1 (0 : Vec d)).mulVec (H ω))
        ≤ Real.exp (2 * L) * L * euclideanNorm (H ω) :=
      isElliptic_mulVec_euclideanNorm_le hLpos hω (0 : Vec d) (H ω)
    have h2 := htri ((ω.1 (0 : Vec d)).mulVec (H ω)) (K ω)
    linarith
  have hmono : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ‖euclideanNorm ((ω.1 (0 : Vec d)).mulVec (H ω) - K ω)‖
        ≤ ‖Real.exp (2 * L) * L * euclideanNorm (H ω) + euclideanNorm (K ω)‖ := by
    filter_upwards [hpt] with ω hω
    have h0 := hN0 ((ω.1 (0 : Vec d)).mulVec (H ω) - K ω)
    have h1 := add_nonneg (mul_nonneg hΛnn (hN0 (H ω))) (hN0 (K ω))
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg h1]
    exact hω
  have hLH : eLpNorm (fun ω => Real.exp (2 * L) * L * euclideanNorm (H ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal (Real.exp (2 * L) * L) *
        eLpNorm (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) := by
    have hae : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        ‖Real.exp (2 * L) * L * euclideanNorm (H ω)‖
          ≤ Real.exp (2 * L) * L * ‖euclideanNorm (H ω)‖ :=
      Filter.Eventually.of_forall fun ω => le_of_eq (by
        rw [Real.norm_of_nonneg (mul_nonneg hΛnn (hN0 (H ω))), Real.norm_of_nonneg (hN0 (H ω))])
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hae _
  have hAm : AEStronglyMeasurable (fun ω => Real.exp (2 * L) * L * euclideanNorm (H ω))
      (reducedEnvironmentLaw Q) :=
    (hHN.const_mul (Real.exp (2 * L) * L)).aestronglyMeasurable
  have hBm : AEStronglyMeasurable (fun ω => euclideanNorm (K ω)) (reducedEnvironmentLaw Q) :=
    hKN.aestronglyMeasurable
  calc eLpNorm (fun ω => euclideanNorm ((ω.1 (0 : Vec d)).mulVec (H ω) - K ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
        eLpNorm (fun ω => Real.exp (2 * L) * L * euclideanNorm (H ω) + euclideanNorm (K ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) := eLpNorm_mono_ae hmono
    _ ≤ eLpNorm (fun ω => Real.exp (2 * L) * L * euclideanNorm (H ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) +
        eLpNorm (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) :=
        eLpNorm_add_le hAm hBm hp1
    _ ≤ ENNReal.ofReal (Real.exp (2 * L) * L) * ENNReal.ofReal (B * R⁻¹) +
          ENNReal.ofReal (D * R⁻¹) :=
        add_le_add (hLH.trans (mul_le_mul_right hH _)) hK
    _ = ENNReal.ofReal (Real.exp (2 * L) * L * (B * R⁻¹) + D * R⁻¹) := by
        rw [ENNReal.ofReal_add (mul_nonneg hΛnn (mul_nonneg hB hRinv)) (mul_nonneg hD hRinv),
          ENNReal.ofReal_mul hΛnn]
    _ ≤ ENNReal.ofReal (((Real.exp (2 * L) * L) * B + D) * R⁻¹) :=
        ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end EinsteinRelation.Correctors
