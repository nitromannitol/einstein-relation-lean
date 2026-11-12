import EinsteinRelation.Correctors.ShiftedMollifierMeans
import EinsteinRelation.Correctors.UniformTranslatedH2Tests
import EinsteinRelation.Correctors.LocalMollifierSpatialTest
import EinsteinRelation.Correctors.PairedPDEAmplitude
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Rescaled planar mollifier pairings

Source: `paper/main.tex:948–955`. The physical convolution at scale `R`
is an AKM unit-ball test after dilation by `4R`. Both the Jacobian and the
conversion from an integral to a normalized average are explicit.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The exact planar change of variables for a rescaled kernel.
Source: `paper/main.tex:948–955`. -/
theorem convolution_rescaled_eq_integral (F ψ : Vec 2 → ℝ)
    {R : ℝ} (hR : 0 < R) (y : Vec 2) :
    (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun z => R ^ (-(2 : ℤ)) * ψ (R⁻¹ • z))) y =
      16 * ∫ x, F ((4 * R) • x) * ψ (R⁻¹ • y - (4 : ℝ) • x) := by
  have hchange := Measure.integral_comp_smul_of_nonneg volume
    (fun z => F z * ψ (R⁻¹ • (y - z))) (4 * R) (hR := by positivity)
  have harg (x : Vec 2) : R⁻¹ • (y - (4 * R) • x) =
      R⁻¹ • y - (4 : ℝ) • x := by
    rw [smul_sub, smul_smul]
    congr 1
    field_simp
  simp only [harg, Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at hchange
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (F _) (R ^ (-(2 : ℤ))) ]
  rw [integral_const_mul, hchange]
  rw [zpow_neg, zpow_ofNat]
  field_simp
  ring

/-- The rescaled pairing is supported inside the AKM unit ball whenever
the kernel is supported in the physical unit ball and `|y| ≤ R`.
Source: `paper/main.tex:948–955`. -/
theorem convolution_rescaled_eq_unit_average (F ψ : Vec 2 → ℝ)
    {R : ℝ} (hR : 0 < R) (y : Vec 2) (hy : euclideanNorm y ≤ R)
    (hsupp : Function.support ψ ⊆ originBall 2 1) :
    (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun z => R ^ (-(2 : ℤ)) * ψ (R⁻¹ • z))) y =
      16 * (volume (originBall 2 1)).toReal *
        (⨍ x in originBall 2 1,
          F ((4 * R) • x) * ψ (R⁻¹ • y - (4 : ℝ) • x)) := by
  have hzero (x : Vec 2) (hx : x ∉ originBall 2 1) :
      ψ (R⁻¹ • y - (4 : ℝ) • x) = 0 := by
    by_contra hn
    have hb := hsupp hn
    change euclideanNorm (R⁻¹ • y - (4 : ℝ) • x) < 1 at hb
    have hy' : euclideanNorm (R⁻¹ • y) ≤ 1 := by
      rw [euclideanNorm_smul _ (inv_nonneg.mpr hR.le)]
      exact (inv_mul_le_one₀ hR).mpr hy
    have ht := TimeChange.euclideanNorm_add_le
      ((4 : ℝ) • x - R⁻¹ • y) (R⁻¹ • y)
    rw [sub_add_cancel, euclideanNorm_smul _ (by norm_num)] at ht
    have he : euclideanNorm ((4 : ℝ) • x - R⁻¹ • y) =
        euclideanNorm (R⁻¹ • y - (4 : ℝ) • x) := by
      rw [← neg_sub (R⁻¹ • y), TimeChange.euclideanNorm_eq_norm_toLp,
        WithLp.toLp_neg, norm_neg, ← TimeChange.euclideanNorm_eq_norm_toLp]
    rw [he] at ht
    have hx' : 1 ≤ euclideanNorm x := not_lt.mp hx
    linarith
  have hset : (∫ x in originBall 2 1,
      F ((4 * R) • x) * ψ (R⁻¹ • y - (4 : ℝ) • x)) =
      ∫ x, F ((4 * R) • x) * ψ (R⁻¹ • y - (4 : ℝ) • x) := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hzero x hx, mul_zero])
  have hv : 0 < (volume (originBall 2 1)).toReal := by
    simpa only [measureReal_def, ball, originBall, sub_zero] using
      paired_ball_volume_pos_finite (d := 2) (R := 1) zero_lt_one
  rw [convolution_rescaled_eq_integral F ψ hR y, average_eq,
    measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, hset]
  field_simp

/-- Compression by four leaves the reflected kernel in the half ball.
Source: `paper/main.tex:948–955`. -/
theorem tsupport_planar_compressed_kernel_subset {ψ : Vec 2 → ℝ}
    (hsupp : tsupport ψ ⊆ originBall 2 1) :
    tsupport (fun x => ψ ((-4 : ℝ) • x)) ⊆ originBall 2 (1/2) := by
  intro x hx
  have hx' := tsupport_comp_subset_preimage ψ
    (continuous_const.smul continuous_id) hx
  have hn := hsupp hx'
  change euclideanNorm ((-4 : ℝ) • x) < 1 at hn
  have he : euclideanNorm ((-4 : ℝ) • x) = 4 * euclideanNorm x := by
    simp only [TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_smul, norm_smul,
      Real.norm_eq_abs]
    norm_num
  rw [he] at hn
  change euclideanNorm x < 1/2
  linarith

/-- Shrinking and reflecting the fixed kernel leaves room for all shifts
of size at most one quarter inside the AKM unit test ball.
Source: `paper/main.tex:948–955`. -/
theorem isSpatialTest_planar_scaled_translate {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ originBall 2 1) {z : Vec 2}
    (hz : euclideanNorm z ≤ 1) :
    IsSpatialTest (originBall 2 1) (fun x => ψ (z - (4 : ℝ) • x)) := by
  let ζ : Vec 2 → ℝ := fun x => ψ ((-4 : ℝ) • x)
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ :=
    hψ.comp (contDiff_const.smul contDiff_id)
  have hζc : HasCompactSupport ζ :=
    hc.comp_homeomorph (Homeomorph.smul (Units.mk0 (-4 : ℝ) (by norm_num)))
  have hζs : tsupport ζ ⊆ originBall 2 (1/2) :=
    tsupport_planar_compressed_kernel_subset hsupp
  have hshift : euclideanNorm ((1/4 : ℝ) • z) ≤ 1/2 := by
    rw [euclideanNorm_smul _ (by norm_num)]
    linarith
  have heq : (fun x => ζ (x - (1/4 : ℝ) • z)) =
      (fun x => ψ (z - (4 : ℝ) • x)) := by
    funext x
    change ψ ((-4 : ℝ) • (x - (1/4 : ℝ) • z)) = ψ (z - (4 : ℝ) • x)
    congr 1
    module
  rw [← heq]
  exact isSpatialTest_comp_sub_of_half_ball hζ hζc hζs hshift

end EinsteinRelation.Correctors
