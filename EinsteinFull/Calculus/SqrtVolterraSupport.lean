import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# A short-time square-root Volterra estimate

The elementary inequality `sqrt t ≤ sqrt s + sqrt (t-s)` bounds the beta
kernel by a sum of two integrable inverse square roots. Maximizing the
continuous weighted unknown then permits absorption on a short interval.
-/

open MeasureTheory Set

noncomputable section
namespace EinsteinFull

/-- The inverse square root is integrable from zero, including its singular endpoint. -/
theorem intervalIntegrable_inv_sqrt {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s : ℝ => (Real.sqrt s)⁻¹) volume 0 t := by
  apply IntervalIntegrable.congr (f := fun s : ℝ => s ^ (-(1/2 : ℝ))) ?_
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  intro s hs
  rw [uIoc_of_le ht] at hs
  change s ^ (-(1/2 : ℝ)) = (Real.sqrt s)⁻¹
  rw [Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]

/-- The integral of the inverse square root has its exact endpoint value. -/
theorem integral_inv_sqrt {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, (Real.sqrt s)⁻¹) = 2 * Real.sqrt t := by
  have he : (∫ s in (0 : ℝ)..t, (Real.sqrt s)⁻¹) =
      ∫ s in (0 : ℝ)..t, s ^ (-(1/2 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    change (Real.sqrt s)⁻¹ = s ^ (-(1/2 : ℝ))
    rw [Real.rpow_neg hs.1, ← Real.sqrt_eq_rpow]
  rw [he, integral_rpow (Or.inl (by norm_num))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

private theorem sqrt_sub_kernel_le {t s M v : ℝ} (hs : 0 < s) (hst : s < t)
    (hM : 0 ≤ M) (hv : Real.sqrt s * v ≤ M) :
    v / Real.sqrt (t-s) ≤
      M / Real.sqrt t * ((Real.sqrt s)⁻¹ + (Real.sqrt (t-s))⁻¹) := by
  have ht : 0 < t := hs.trans hst
  have hx : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hy : 0 < Real.sqrt (t-s) := Real.sqrt_pos.2 (sub_pos.2 hst)
  have hz : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hadd : Real.sqrt t ≤ Real.sqrt s + Real.sqrt (t-s) := by
    nlinarith only [Real.sq_sqrt hs.le, Real.sq_sqrt (sub_nonneg.2 hst.le),
      Real.sq_sqrt ht.le, mul_nonneg hx.le hy.le, hx, hy, hz]
  calc
    v / Real.sqrt (t-s) ≤ (M / Real.sqrt s) / Real.sqrt (t-s) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hx).2 (by simpa only [mul_comm] using hv)) hy.le
    _ ≤ M / Real.sqrt t * ((Real.sqrt s)⁻¹ + (Real.sqrt (t-s))⁻¹) := by
      field_simp
      simpa only [add_comm] using mul_le_mul_of_nonneg_left hadd hM

/-- A square-root weighted bound controls the entire singular convolution by four times its amplitude. -/
theorem integral_div_sqrt_sub_le {v : ℝ → ℝ} (hv : Continuous v)
    {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Ioc 0 t, Real.sqrt s * v s ≤ M) :
    (∫ s in (0 : ℝ)..t, v s / Real.sqrt (t-s)) ≤ 4 * M := by
  have hi := intervalIntegrable_inv_sqrt ht.le
  have hj : IntervalIntegrable (fun s : ℝ => (Real.sqrt (t-s))⁻¹) volume 0 t := by
    simpa only [sub_zero, sub_self] using (hi.comp_sub_left t).symm
  have hvint : IntervalIntegrable (fun s => v s / Real.sqrt (t-s)) volume 0 t := by
    simpa only [div_eq_mul_inv, mul_comm] using hj.mul_continuousOn hv.continuousOn
  have he : (∫ s in (0 : ℝ)..t, (Real.sqrt (t-s))⁻¹) = 2 * Real.sqrt t := by
    change (∫ s in (0 : ℝ)..t, (fun x => (Real.sqrt x)⁻¹) (t-s)) = _
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => (Real.sqrt x)⁻¹) t]
    simpa only [sub_self, sub_zero] using integral_inv_sqrt ht.le
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, M / Real.sqrt t *
        ((Real.sqrt s)⁻¹ + (Real.sqrt (t-s))⁻¹) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hvint
        ((hi.add hj).const_mul _) (fun s hs => ?_)
      exact sqrt_sub_kernel_le hs.1 hs.2 hM (hbound s ⟨hs.1, hs.2.le⟩)
    _ = 4 * M := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi hj,
        integral_inv_sqrt ht.le, he]
      field_simp
      ring

/-- Absorption of the singular convolution gives a short-time bound independent of the initial value. -/
theorem sqrt_volterra_le_of_small {v : ℝ → ℝ} (hv : Continuous v)
    {A B T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 < T)
    (hnonneg : ∀ s ∈ Icc 0 T, 0 ≤ v s)
    (hsmall : 8 * B * Real.sqrt T ≤ 1)
    (hvolterra : ∀ t ∈ Ioc 0 T, v t ≤ A / Real.sqrt t +
      B * (∫ s in (0 : ℝ)..t, v s / Real.sqrt (t-s))) :
    ∀ t ∈ Ioc 0 T, v t ≤ 2 * A / Real.sqrt t := by
  obtain ⟨τ, hτ, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT.le)
    ((Real.continuous_sqrt.mul hv).continuousOn)
  let M := Real.sqrt τ * v τ
  have hM : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) (hnonneg τ hτ)
  have hbound : ∀ s ∈ Icc 0 T, Real.sqrt s * v s ≤ M := hmax
  have hMbound : M ≤ 2 * A := by
    by_cases hτ0 : τ = 0
    · simp only [M, hτ0, Real.sqrt_zero, zero_mul]
      positivity
    have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτ0)
    have hconv := integral_div_sqrt_sub_le hv hτpos hM
      (fun s hs => hbound s ⟨hs.1.le, hs.2.trans hτ.2⟩)
    have hle := mul_le_mul_of_nonneg_left
      ((hvolterra τ ⟨hτpos, hτ.2⟩).trans
        (add_le_add_right (mul_le_mul_of_nonneg_left hconv hB) _))
      (Real.sqrt_nonneg τ)
    have hsqrt : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτpos
    have hcoef : 8 * B * Real.sqrt τ ≤ 1 :=
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hτ.2)
        (mul_nonneg (by norm_num) hB)).trans hsmall
    have habs : 4 * B * Real.sqrt τ * M ≤ M / 2 := by
      have hm := mul_le_mul_of_nonneg_right hcoef hM
      nlinarith only [hm]
    dsimp only [M] at hle ⊢
    rw [mul_add, mul_div_cancel₀ _ hsqrt.ne'] at hle
    dsimp only [M] at habs
    nlinarith only [hle, habs]
  intro t ht
  apply (le_div_iff₀ (Real.sqrt_pos.2 ht.1)).2
  have hpoint : v t * Real.sqrt t ≤ M := by
    simpa only [mul_comm] using hbound t ⟨ht.1.le, ht.2⟩
  exact hpoint.trans hMbound

end EinsteinFull
