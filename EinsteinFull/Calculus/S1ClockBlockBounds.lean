import EinsteinFull.Calculus.S1ClockBlockSupport

/-! Second-moment bounds for the clock coordinate of the localized covariance block:
full cube (CLT order) and boundary strip (surface-area gain). -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1
open EinsteinFull EinsteinRelation EinsteinRelation.External.AKM
open EinsteinFull.Blueprint

theorem clock_block_eq (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (s δ γ η β : ℝ)
    (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) {r : ℝ} (hr : 0 < r)
    (x : Vec d) (L : ℝ) (f : Vec d → ℝ) (ω : FieldPair d) :
    covarianceBlock d hd D s δ γ η β h Q r L L x f ω (Sum.inr ()) =
      L ^ (-(d : ℝ) / 2) * ∫ y in clockBlockCube x L, f y *
        ∫ z in ball (0 : Vec d) (covarianceLocalizationRadius D δ r),
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z * centeredClockField Q (y - z) ω := by
  simp only [covarianceBlock, covarianceLocalizedField, heatKernel_eq_anisotropic r hr]

theorem clock_block_sq_le (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (s δ γ η β : ℝ)
    (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) {r : ℝ} (hr : 0 < r)
    (x : Vec d) {L : ℝ} (hL : 0 < L) {f : Vec d → ℝ} (hfm : Measurable f) {b : ℝ}
    (hb : 0 ≤ b) (hfb : ∀ y ∈ clockBlockCube x L, |f y| ≤ b) :
    ∫ ω, (covarianceBlock d hd D s δ γ η β h Q r L L x f ω (Sum.inr ())) ^ 2 ∂reducedLaw Q ≤
      clockVarianceConstant d D.ellipticity D.dependenceRange * b ^ 2 := by
  have hW := clockCube_anisotropicGaussian_variance_le Q ((2 : ℝ) • (1 : Mat d))
    two_smul_one_posDef (r ^ 2) (by positivity)
    (measurableSet_ball_zero (covarianceLocalizationRadius D δ r)) x hL.le hfm hb hfb
  simp_rw [clock_block_eq d hd D s δ γ η β h Q hr x L f, mul_pow]
  rw [integral_const_mul]
  calc (L ^ (-(d : ℝ) / 2)) ^ 2 * ∫ ω, (∫ y in clockBlockCube x L, f y *
        ∫ z in ball (0 : Vec d) (covarianceLocalizationRadius D δ r),
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z *
            centeredClockField Q (y - z) ω) ^ 2 ∂reducedLaw Q
      ≤ (L ^ (-(d : ℝ) / 2)) ^ 2 *
        (clockVarianceConstant d D.ellipticity D.dependenceRange * b ^ 2 * L ^ d) :=
        mul_le_mul_of_nonneg_left hW (sq_nonneg _)
    _ = clockVarianceConstant d D.ellipticity D.dependenceRange * b ^ 2 *
        ((L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ d) := by ring
    _ = _ := by rw [rpow_neg_half_sq_mul_pow hL d, mul_one]

theorem clock_strip_sq_le (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (s δ γ η β : ℝ)
    (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) {r : ℝ} (hr : 0 < r)
    (x : Vec d) {L w : ℝ} (hL : 0 < L) (hw : 0 ≤ w) (hwL : w ≤ L)
    {f : Vec d → ℝ} (hfm : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hfb : ∀ y ∈ clockBlockCube x L, |f y| ≤ b)
    (hf0 : ∀ y ∈ clockBlockCube x (L - w), f y = 0) :
    ∫ ω, (covarianceBlock d hd D s δ γ η β h Q r L L x f ω (Sum.inr ())) ^ 2 ∂reducedLaw Q ≤
      clockVarianceConstant d D.ellipticity D.dependenceRange * b ^ 2 * (d * w / L) := by
  have hW := clockCube_strip_anisotropicGaussian_variance_le Q ((2 : ℝ) • (1 : Mat d))
    two_smul_one_posDef (r ^ 2) (by positivity)
    (measurableSet_ball_zero (covarianceLocalizationRadius D δ r)) x hw hwL hfm hb
    (fun y hy => hfb y hy.1)
  have hstrip : ∀ ω, covarianceBlock d hd D s δ γ η β h Q r L L x f ω (Sum.inr ()) =
      L ^ (-(d : ℝ) / 2) * ∫ y in clockBlockCube x L \ clockBlockCube x (L - w), f y *
        ∫ z in ball (0 : Vec d) (covarianceLocalizationRadius D δ r),
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z *
            centeredClockField Q (y - z) ω := by
    intro ω
    rw [clock_block_eq d hd D s δ γ η β h Q hr x L f ω]
    congr 1
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_clockBlockCube x L)
      Set.sdiff_subset ?_
    intro y hy
    have hin : y ∈ clockBlockCube x (L - w) := by
      by_contra hn
      exact hy.2 ⟨hy.1, hn⟩
    simp [hf0 y hin]
  simp_rw [hstrip, mul_pow]
  rw [integral_const_mul]
  have hLd : L ^ d = L * L ^ (d - 1) := by
    rw [← pow_succ' L (d - 1)]
    congr 1
    omega
  have hcoef : (L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ (d - 1) = L⁻¹ := by
    have h1 := rpow_neg_half_sq_mul_pow hL d
    rw [hLd] at h1
    refine eq_inv_of_mul_eq_one_left ?_
    calc (L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ (d - 1) * L
        = (L ^ (-(d : ℝ) / 2)) ^ 2 * (L * L ^ (d - 1)) := by ring
      _ = 1 := h1
  calc (L ^ (-(d : ℝ) / 2)) ^ 2 * ∫ ω, (∫ y in clockBlockCube x L \ clockBlockCube x (L - w),
        f y * ∫ z in ball (0 : Vec d) (covarianceLocalizationRadius D δ r),
          anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) z *
            centeredClockField Q (y - z) ω) ^ 2 ∂reducedLaw Q
      ≤ (L ^ (-(d : ℝ) / 2)) ^ 2 *
        (clockVarianceConstant d D.ellipticity D.dependenceRange * b ^ 2 *
          (d * L ^ (d - 1) * w)) := mul_le_mul_of_nonneg_left hW (sq_nonneg _)
    _ = clockVarianceConstant d D.ellipticity D.dependenceRange * b ^ 2 * d * w *
        ((L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ (d - 1)) := by ring
    _ = _ := by rw [hcoef]; field_simp

end EinsteinFull.Calculus.S1
