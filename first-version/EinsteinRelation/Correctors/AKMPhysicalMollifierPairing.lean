import EinsteinRelation.Correctors.MollifierDilationTransport
import EinsteinRelation.Correctors.RescaledMollifierPairing

/-! # The physical planar test on the AKM unit ball

Source: `paper/main.tex:789–810,948–955`. Physical radii begin at one,
whereas AKM radii begin at `r₀⁻¹`. Compressing the fixed test by `4r₀`
keeps the AKM small parameter below one half throughout that range.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The exact normalized-source pairing for a physical mollifier at radius
`R`, with range `r ≥ 1`. Source: `paper/main.tex:948–955`. -/
theorem convolution_source_eq_physical_unit_average (F : Vec 2 → ℝ)
    {r R : ℝ} (hr : 1 ≤ r) (hR : 0 < R) (y : Vec 2) (hy : euclideanNorm y ≤ R) :
    (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Calculus.unitMassScaledMollifier 2 (R / r)) (r⁻¹ • y) =
      (16 * r ^ 2 * (volume (originBall 2 1)).toReal) *
        (⨍ x in originBall 2 1,
          F ((4 * R) • x) * mollifier 2 (R⁻¹ • y - (4 * r) • x)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  let ψ : Vec 2 → ℝ := fun x => r ^ 2 * mollifier 2 (r • x)
  have hsupp : Function.support ψ ⊆ originBall 2 1 := by
    intro x hx
    have hm : mollifier 2 (r • x) ≠ 0 := by
      intro hz
      exact hx (by simp only [ψ, hz, mul_zero])
    have hnorm := (tsupport_mollifier_subset 2) (subset_tsupport _ hm)
    change euclideanNorm (r • x) < 1 at hnorm
    rw [euclideanNorm_smul _ hr0.le] at hnorm
    have hn := (show 0 ≤ euclideanNorm x from Real.sqrt_nonneg _)
    change euclideanNorm x < 1
    nlinarith
  have hy' : euclideanNorm (r⁻¹ • y) ≤ R := by
    rw [euclideanNorm_smul _ (inv_nonneg.mpr hr0.le)]
    calc r⁻¹ * euclideanNorm y ≤ r⁻¹ * R :=
        mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hr0.le)
      _ ≤ R := mul_le_of_le_one_left hR.le ((inv_le_one₀ hr0).mpr hr)
  have hkernel : (fun z : Vec 2 => R ^ (-(2 : ℤ)) * ψ (R⁻¹ • z)) =
      Calculus.unitMassScaledMollifier 2 (R / r) := by
    funext z
    dsimp only [ψ, Calculus.unitMassScaledMollifier]
    rw [zpow_neg, zpow_ofNat, div_pow, inv_div, inv_div, smul_smul]
    have ha : r * R⁻¹ = r / R := by ring
    rw [ha]
    field_simp
  have h := convolution_rescaled_eq_unit_average F ψ hR (r⁻¹ • y) hy' hsupp
  rw [hkernel] at h
  have harg (x : Vec 2) : r • (R⁻¹ • (r⁻¹ • y) - (4 : ℝ) • x) =
      R⁻¹ • y - (4 * r) • x := by
    rw [smul_sub, smul_smul, smul_smul, smul_smul]
    have ha : r * R⁻¹ * r⁻¹ = R⁻¹ := by field_simp
    rw [ha, mul_comm r 4]
  simp only [ψ, harg, mul_left_comm (F _) (r ^ 2), average_eq,
    integral_const_mul, smul_eq_mul] at h
  rw [h]
  simp only [average_eq, smul_eq_mul]
  ring

/-- The source test compressed by the physical range has compact support
inside the AKM half ball. Source: `paper/main.tex:948–955`. -/
theorem tsupport_physical_compressed_mollifier {r : ℝ} (hr : 1 ≤ r) :
    tsupport (fun x : Vec 2 => mollifier 2 ((-(4 * r)) • x)) ⊆ originBall 2 (1/2) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  intro x hx
  have h := (tsupport_mollifier_subset 2)
    (tsupport_comp_subset_preimage (mollifier 2) (continuous_const.smul continuous_id) hx)
  change euclideanNorm ((-(4 * r)) • x) < 1 at h
  have hn : euclideanNorm ((-(4 * r)) • x) = (4 * r) * euclideanNorm x := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_smul, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity),
      ← TimeChange.euclideanNorm_eq_norm_toLp]
  rw [hn] at h
  change euclideanNorm x < 1/2
  have := (show 0 ≤ euclideanNorm x from Real.sqrt_nonneg _)
  nlinarith

end EinsteinRelation.Correctors
