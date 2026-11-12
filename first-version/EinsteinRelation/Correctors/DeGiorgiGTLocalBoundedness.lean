import Mathlib
import EinsteinRelation.External.GilbargTrudinger
import DeGiorgi.NormalizedRegularity
import DeGiorgi.Localization
import EinsteinRelation.Correctors.DeGiorgiBallPreimage
import EinsteinRelation.Correctors.EuclideanSetIntegralTransport
import EinsteinRelation.Correctors.EuclideanMemLpTransport
import EinsteinRelation.Correctors.DeGiorgiEllipticCoeff
import EinsteinRelation.Correctors.DeGiorgiWeakSolutionTransport
import EinsteinRelation.Correctors.EuclideanBallAeTransport
import EinsteinRelation.Correctors.TwoSidedMoserBound
import EinsteinRelation.Correctors.DeGiorgiTwoSidedMoser
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-!
# Local boundedness from the De Giorgi–Moser bound

The homogeneous Gilbarg–Trudinger estimate (Theorem 8.17, (8.46), p. 194) is derived from the
De Giorgi `L^p → L^∞` bound on Euclidean balls. A Gilbarg–Trudinger weak solution on an open set
containing `ball y (2 * R)` restricts to a homogeneous De Giorgi solution on the Euclidean ball
of radius `2 * R`, with coefficient field of ellipticity ratio `(Λ ^ 2 / lam) / lam`. The
two-sided Moser bounds for `u` and `-u` and the scalar inequality
`abs_le_of_two_sided_moser_bound` give the pointwise estimate on the ball of radius `R`. The
coordinate ball is identified with the Euclidean ball by the measure-preserving `WithLp.ofLp`.
-/

theorem localBoundednessEstimate_of_deGiorgi :
    External.GilbargTrudinger.LocalBoundednessEstimate := by
  intro d hd lam Λ p hlam _ hp
  haveI : NeZero d := ⟨by omega⟩
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hr : 0 ≤ (Λ ^ 2 / lam) / lam := div_nonneg (div_nonneg (sq_nonneg Λ) hlam.le) hlam.le
  have hC0 : 0 ≤ DeGiorgi.C_Moser d :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (DeGiorgi.one_le_C_Moser (d := d))
  -- The constant depends only on `d, lam, Λ, p`, and is fixed before the data `U, a, u, y, R`.
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max 1 ((DeGiorgi.C_Moser d *
      ((Λ ^ 2 / lam) / lam) ^ (DeGiorgi.sobolevDim d / 2) *
      (p / (p - 1)) ^ DeGiorgi.sobolevDim d * (2 ^ d)⁻¹) ^ (1 / p)) := ⟨_, rfl⟩
  have hCpos : 0 < C := by
    rw [hCdef]
    exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have hCle : (DeGiorgi.C_Moser d *
      ((Λ ^ 2 / lam) / lam) ^ (DeGiorgi.sobolevDim d / 2) *
      (p / (p - 1)) ^ DeGiorgi.sobolevDim d * (2 ^ d)⁻¹) ^ (1 / p) ≤ C := by
    rw [hCdef]
    exact le_max_right _ _
  have hK : 0 ≤ DeGiorgi.C_Moser d * ((Λ ^ 2 / lam) / lam) ^ (DeGiorgi.sobolevDim d / 2) *
      (p / (p - 1)) ^ DeGiorgi.sobolevDim d :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hr _))
      (Real.rpow_nonneg (div_nonneg hp0.le hp1) _)
  refine ⟨C, hCpos, ?_⟩
  intro U _ a ha u _ hsol y R hR hB hu
  have hR2 : 0 < 2 * R := by linarith
  have hyball : y ∈ External.AKM.ball y (2 * R) := by
    show euclideanNorm (y - y) < 2 * R
    have h0 : euclideanNorm (y - y) = 0 := by simp [euclideanNorm, euclideanSq, dot]
    rw [h0]
    exact hR2
  -- The De Giorgi coefficient field on the Euclidean ball of radius `2 * R`.
  obtain ⟨A, hAa, hAlam, hAΛ⟩ := exists_ellipticCoeff_of_ellipticBound hlam ha hB ⟨y, hyball⟩
  have hsolA := isHomogeneousWeakSolution_of_weakSolution ha hsol hB A hAa
  -- Integrability of `|u|^p` on the Euclidean ball, from `MemLp u p` on the coordinate ball.
  have hint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => |u (WithLp.ofLp x)| ^ p)
      (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) (2 * R)) volume := by
    have hmem := (memLp_comp_ofLp_iff (External.AKM.ball y (2 * R)) u (ENNReal.ofReal p)).mpr hu
    rw [preimage_ofLp_ball] at hmem
    have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
    have hint' := hmem.integrable_norm_rpow hpne ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hp0.le] at hint'
    simp only [Real.norm_eq_abs] at hint'
    exact hint'
  -- The two one-sided Moser bounds on the Euclidean ball of radius `R`.
  have hM : ∀ᵐ x ∂(volume.restrict (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R)),
      |max (u (WithLp.ofLp x)) 0| ^ p ≤
          (DeGiorgi.C_Moser d * ((Λ ^ 2 / lam) / lam) ^ (DeGiorgi.sobolevDim d / 2) *
            (p / (p - 1)) ^ DeGiorgi.sobolevDim d) *
          (((2 * R) ^ d)⁻¹ * ∫ z in
            Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) (2 * R),
            |u (WithLp.ofLp z)| ^ p) ∧
        |max (-u (WithLp.ofLp x)) 0| ^ p ≤
          (DeGiorgi.C_Moser d * ((Λ ^ 2 / lam) / lam) ^ (DeGiorgi.sobolevDim d / 2) *
            (p / (p - 1)) ^ DeGiorgi.sobolevDim d) *
          (((2 * R) ^ d)⁻¹ * ∫ z in
            Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) (2 * R),
            |u (WithLp.ofLp z)| ^ p) := by
    have h := posPart_negPart_rpow_le_of_isHomogeneousWeakSolution hd hR A hp hsolA hint
    have hratio : DeGiorgi.ellipticityRatio A = (Λ ^ 2 / lam) / lam := by
      show A.Λ / A.lam = _
      rw [hAΛ, hAlam]
    rw [hratio] at h
    exact h
  have hJnn : 0 ≤ ∫ z in Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) (2 * R),
      |u (WithLp.ofLp z)| ^ p :=
    integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hJvec : 0 ≤ ∫ z in External.AKM.ball y (2 * R), |u z| ^ p :=
    integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  -- Change of variables from the Euclidean ball to the coordinate ball `ball y (2 * R)`.
  have hJeq : (∫ x in Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) (2 * R),
      |u (WithLp.ofLp x)| ^ p) = ∫ z in External.AKM.ball y (2 * R), |u z| ^ p := by
    have h := setIntegral_comp_ofLp (External.AKM.ball y (2 * R)) (fun z => |u z| ^ p)
    rw [preimage_ofLp_ball] at h
    exact h
  -- The pointwise bound on the Euclidean ball of radius `R`.
  have hfinal :
      ∀ᵐ x ∂(volume.restrict (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R)),
        |u (WithLp.ofLp x)| ≤
          C * R ^ (-(d : ℝ) / p) * (∫ z in External.AKM.ball y (2 * R), |u z| ^ p) ^ (1 / p) := by
    filter_upwards [hM] with x hx
    have h := abs_le_of_two_sided_moser_bound hp0 hR hK hJnn hx.1 hx.2
    rw [hJeq] at h
    have hRpow : 0 ≤ R ^ (-(d : ℝ) / p) := Real.rpow_nonneg hR.le _
    have hJpow : 0 ≤ (∫ z in External.AKM.ball y (2 * R), |u z| ^ p) ^ (1 / p) :=
      Real.rpow_nonneg hJvec _
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hRpow) hJpow)
  -- Transfer the almost-everywhere bound to the coordinate ball `External.AKM.ball y R`.
  exact (ae_restrict_ball_comp_ofLp_iff y R
    (fun v => |u v| ≤ C * R ^ (-(d : ℝ) / p) *
      (∫ z in External.AKM.ball y (2 * R), |u z| ^ p ∂volume) ^ (1 / p))).mp hfinal

end EinsteinRelation.Correctors
