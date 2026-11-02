import EinsteinFull.External.Source.GMPDirichletKernel

open EinsteinRelation

namespace EinsteinFull

/-- Translation and positive time scaling preserve the source ellipticity bounds,
with a constant uniform in the coefficient fields and translation. -/
theorem c13_uniform_ellipticity_affine_time_transport {d : ℕ} (kappa h : ℝ)
    (hkappa : 0 < kappa) (hh : 0 < h) :
    ∃ kappa' : ℝ, 0 < kappa' ∧ ∀ (rho : Vec d → ℝ) (alpha : Vec d → Mat d),
      External.Source.GMP.IsUniformlyElliptic kappa rho alpha → ∀ y : Vec d,
      External.Source.GMP.IsUniformlyElliptic kappa' (fun x => rho (x + y))
        (fun x => h • alpha (x + y)) := by
  let m : ℝ := min 1 (min h h⁻¹)
  have hm : 0 < m := lt_min zero_lt_one (lt_min hh (inv_pos.mpr hh))
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmh : m ≤ h := (min_le_right _ _).trans (min_le_left _ _)
  have hmi : m ≤ h⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hhm : h * m ≤ 1 := by
    calc
      h * m ≤ h * h⁻¹ := mul_le_mul_of_nonneg_left hmi hh.le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hh)
  let kp := kappa * m
  have hkp : 0 < kp := mul_pos hkappa hm
  have hkpK : kp ≤ kappa := by dsimp [kp]; nlinarith
  have hkpH : kp ≤ h * kappa := by dsimp [kp]; nlinarith
  have hhkp : h * kp ≤ kappa := by dsimp [kp]; nlinarith [mul_le_mul_of_nonneg_left hhm hkappa.le]
  have hinv : kappa⁻¹ ≤ kp⁻¹ := inv_le_inv₀ hkappa hkp |>.mpr hkpK
  have hhinv : h * kappa⁻¹ ≤ kp⁻¹ := by
    have := mul_le_mul_of_nonneg_right hhkp (le_of_lt (inv_pos.mpr hkappa))
    have := mul_le_mul_of_nonneg_right this (le_of_lt (inv_pos.mpr hkp))
    field_simp at this ⊢
    nlinarith
  refine ⟨kp, hkp, ?_⟩
  intro rho alpha he y
  rcases he with ⟨hr, ha, he⟩
  have ht : Measurable (fun x : Vec d => x + y) := measurable_id.add measurable_const
  have hscale : Continuous (fun A : Mat d => h • A) :=
    continuous_const_smul h
  have hscaled : Measurable (fun x => h • alpha (x + y)) :=
    hscale.measurable.comp (ha.comp ht)
  refine ⟨hr.comp ht, hscaled, ?_⟩
  intro x
  rcases he (x + y) with ⟨hl, hu, hs, hq⟩
  refine ⟨hkpK.trans hl, hu.trans hinv, ?_, ?_⟩
  · simpa only [Matrix.transpose_smul, hs]
  intro v
  have hv : 0 ≤ euclideanSq v := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have heq : dot v ((h • alpha (x + y)).mulVec v) =
      h * dot v ((alpha (x + y)).mulVec v) := by
    rw [Matrix.smul_mulVec]
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    congr 1
    ext i
    ring
  rw [heq]
  constructor
  · calc
      kp * euclideanSq v ≤ (h * kappa) * euclideanSq v := mul_le_mul_of_nonneg_right hkpH hv
      _ = h * (kappa * euclideanSq v) := by ring
      _ ≤ h * dot v ((alpha (x + y)).mulVec v) := mul_le_mul_of_nonneg_left (hq v).1 hh.le
  · calc
      h * dot v ((alpha (x + y)).mulVec v) ≤ h * (kappa⁻¹ * euclideanSq v) :=
        mul_le_mul_of_nonneg_left (hq v).2 hh.le
      _ = (h * kappa⁻¹) * euclideanSq v := by ring
      _ ≤ kp⁻¹ * euclideanSq v := mul_le_mul_of_nonneg_right hhinv hv

end EinsteinFull
