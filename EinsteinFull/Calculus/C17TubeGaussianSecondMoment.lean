import EinsteinFull.Calculus.C5CanonicalMeanSublinearity
import EinsteinFull.External.Source.GMPDirichletSpectralKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open EinsteinRelation MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section
namespace EinsteinFull.Calculus

theorem c17_gaussian_second_moment_integrable (d : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : Vec d => Real.exp (-a * euclideanSq x) * euclideanSq x) := by
  have hp (x : Vec d) : Real.exp (-a * euclideanSq x) =
      ∏ i : Fin d, Real.exp (-a * (x i)^2) := by
    rw [← Real.exp_sum, ← Finset.mul_sum]
    congr 1
    simp only [euclideanSq, dot, pow_two]
  have hs (j : Fin d) : Integrable (fun x : Vec d => x j ^ 2 *
      ∏ i : Fin d, Real.exp (-a * (x i)^2)) := by
    have h (i : Fin d) : Integrable (fun u : ℝ =>
        (if i = j then u ^ 2 else 1) * Real.exp (-a * u^2)) := by
      by_cases hi : i = j
      · simpa only [hi, ite_true, Real.rpow_two] using
          (integrable_rpow_mul_exp_neg_mul_sq (b := a) ha (s := 2) (by norm_num))
      · simpa only [hi, ite_false, one_mul] using (integrable_exp_neg_mul_sq ha)
    simpa only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
      using! Integrable.fintype_prod h
  have hsum : Integrable (fun x : Vec d => ∑ i : Fin d,
      x i ^ 2 * ∏ j : Fin d, Real.exp (-a * (x j)^2)) :=
    integrable_finset_sum _ (fun i _ => hs i)
  convert hsum using 1
  ext x
  rw [hp]
  simp only [euclideanSq, dot, pow_two, Finset.sum_mul, mul_comm]

theorem c17_shifted_gaussian_second_moment_integrable (d : ℕ) (a : ℝ) (ha : 0 < a)
    (x : Vec d) :
    Integrable (fun y : Vec d => Real.exp (-a * euclideanSq (y - x)) *
      euclideanSq (y - x)) := by
  exact (measurePreserving_sub_right (volume : Measure (Vec d)) x).integrable_comp_of_integrable
    (c17_gaussian_second_moment_integrable d a ha)

@[nolint unusedArguments]
theorem c17_gaussian_dominated_second_moment_integrable (d : ℕ)
    (a K B : ℝ) (ha : 0 < a) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (x : Vec d) (k ρ : Vec d → ℝ) (hk : Measurable k) (hρ : Measurable ρ)
    (hkb : ∀ y, 0 ≤ k y ∧ k y ≤ K * Real.exp (-a * euclideanSq (y-x)))
    (hρb : ∀ y, 0 ≤ ρ y ∧ ρ y ≤ B) :
    Integrable (fun y => k y * euclideanSq (y-x) * ρ y) := by
  have hsq : Continuous (fun y : Vec d => euclideanSq (y-x)) := by
    unfold euclideanSq dot
    exact continuous_finset_sum _ (fun i _ =>
      ((continuous_apply i).sub continuous_const).mul ((continuous_apply i).sub continuous_const))
  apply ((c17_shifted_gaussian_second_moment_integrable d a ha x).const_mul (K * B)).mono'
    ((hk.mul hsq.measurable).mul hρ).aestronglyMeasurable
  filter_upwards [] with y
  have hs : 0 ≤ euclideanSq (y-x) := by
    simp only [euclideanSq, dot]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have he := (Real.exp_pos (-a * euclideanSq (y-x))).le
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hkb y).1 hs) (hρb y).1)]
  calc
    k y * euclideanSq (y-x) * ρ y ≤
        (K * Real.exp (-a * euclideanSq (y-x))) * euclideanSq (y-x) * B :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hkb y).2 hs) (hρb y).2
        (hρb y).1 (mul_nonneg (mul_nonneg hK he) hs)
    _ = (K * B) * (Real.exp (-a * euclideanSq (y-x)) * euclideanSq (y-x)) := by ring

private theorem c17_euclideanSq_smul {d : ℕ} (r : ℝ) (x : Vec d) :
    euclideanSq (r • x) = r ^ 2 * euclideanSq x := by
  simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact dilation of the unnormalized Gaussian second moment. -/
theorem c17_gaussian_second_moment_dilation (d : ℕ) (r : ℝ) (hr : 0 < r) :
    (∫ y : Vec d, Real.exp (-euclideanSq y / r^2) * euclideanSq y) =
      r ^ (d + 2) * ∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Vec d))
    (fun z : Vec d => Real.exp (-euclideanSq z) * euclideanSq z) hr.le
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one,
    smul_eq_mul] at h
  have he (y : Vec d) :
      Real.exp (-euclideanSq (r⁻¹ • y)) * euclideanSq (r⁻¹ • y) =
        (r^2)⁻¹ * (Real.exp (-euclideanSq y / r^2) * euclideanSq y) := by
    rw [c17_euclideanSq_smul, inv_pow]
    have hexp : -((r ^ 2)⁻¹ * euclideanSq y) = -euclideanSq y / r ^ 2 := by
      rw [div_eq_mul_inv]
      ring
    rw [hexp]
    ring
  simp_rw [he, integral_const_mul] at h
  have hr2 : r^2 ≠ 0 := pow_ne_zero _ hr.ne'
  calc
    _ = r^2 * ((r^2)⁻¹ * ∫ y : Vec d,
        Real.exp (-euclideanSq y / r^2) * euclideanSq y) := by
          rw [← mul_assoc, mul_inv_cancel₀ hr2, one_mul]
    _ = r^2 * (r^d * ∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z) := by rw [h]
    _ = _ := by rw [pow_add]; ring

/-- Gaussian second moment with an arbitrary center and variance. -/
theorem c17_gaussian_second_moment_formula (d : ℕ) (a : ℝ) (ha : 0 < a)
    (x : Vec d) :
    (∫ y : Vec d, Real.exp (-euclideanSq (y-x) / a) * euclideanSq (y-x)) =
      Real.rpow a ((d : ℝ) / 2 + 1) *
        ∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z := by
  have ht : (∫ y : Vec d, Real.exp (-euclideanSq (y-x) / a) * euclideanSq (y-x)) =
      ∫ y : Vec d, Real.exp (-euclideanSq y / a) * euclideanSq y := by
    have hm : MeasurableEmbedding (fun y : Vec d => y - x) := by
      simpa only [sub_eq_add_neg, Homeomorph.coe_addRight] using
        (Homeomorph.addRight (-x)).measurableEmbedding
    exact (measurePreserving_sub_right (volume : Measure (Vec d)) x).integral_comp hm
      (fun z => Real.exp (-euclideanSq z / a) * euclideanSq z)
  rw [ht]
  have hs := c17_gaussian_second_moment_dilation d (Real.sqrt a) (Real.sqrt_pos.2 ha)
  rw [Real.sq_sqrt ha.le] at hs
  rw [hs]
  congr 1
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le]
  congr 1
  push_cast
  ring

private theorem c17_gaussian_scale_algebra (d : ℕ) (C t : ℝ) (hC : 0 < C) (ht : 0 < t) :
    (C * Real.rpow t (-(d : ℝ) / 2)) * Real.rpow (C*t) ((d : ℝ)/2+1) =
      Real.rpow C ((d : ℝ)/2+2) * t := by
  change C * t ^ (-(d : ℝ)/2) * (C*t) ^ ((d : ℝ)/2+1) =
    C ^ ((d : ℝ)/2+2) * t
  rw [Real.mul_rpow hC.le ht.le]
  have ht' : t ^ (-(d : ℝ)/2) * t ^ ((d : ℝ)/2+1) = t := by
    rw [← Real.rpow_add ht]
    convert Real.rpow_one t using 1 <;> ring
  have hC' : C * C ^ ((d : ℝ)/2+1) = C ^ ((d : ℝ)/2+2) := by
    calc
      _ = C ^ (1 : ℝ) * C ^ ((d : ℝ)/2+1) := by rw [Real.rpow_one]
      _ = C ^ (1 + ((d : ℝ)/2+1)) := (Real.rpow_add hC _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (C * C ^ ((d : ℝ)/2+1)) *
        (t ^ (-(d : ℝ)/2) * t ^ ((d : ℝ)/2+1)) := by ring
    _ = _ := by rw [hC', ht']

/-- A Gaussian upper bound gives the density-weighted spatial second moment. -/
@[nolint unusedArguments]
theorem c17_gaussian_kernel_second_moment (d : ℕ) (hd : 2 ≤ d) :
 ∃ D : ℝ, 0 < D ∧ ∀ (ρ : Vec d → ℝ) (hρ : Measurable ρ)
 (B : ℝ), 0 < B → (∀ y, 0 ≤ ρ y ∧ ρ y ≤ B) →
 ∀ (C t : ℝ), 0 < C → 0 < t → ∀ (x : Vec d) (k : Vec d → ℝ),
 Measurable k → (∀ y, 0 ≤ k y ∧ k y ≤
 C * Real.rpow t (-(d:ℝ)/2) * Real.exp (-euclideanSq (y-x)/(C*t))) →
 (∫ y, k y * euclideanSq (y-x) * ρ y) ≤
 D * B * Real.rpow C ((d:ℝ)/2+2) * t := by
  let S : ℝ := ∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z
  have hS : 0 ≤ S := by
    apply integral_nonneg
    intro z
    apply mul_nonneg (Real.exp_pos _).le
    simp only [euclideanSq, dot]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  refine ⟨S + 1, by linarith, ?_⟩
  intro ρ hρ B hB hρb C t hC ht x k hk hkb
  let K := C * Real.rpow t (-(d : ℝ)/2)
  have hK : 0 ≤ K := mul_nonneg hC.le (Real.rpow_nonneg ht.le _)
  have hCt : 0 < C*t := mul_pos hC ht
  have hkb' : ∀ y, 0 ≤ k y ∧ k y ≤ K * Real.exp (-(C*t)⁻¹ * euclideanSq (y-x)) := by
    intro y
    convert hkb y using 1 <;> simp only [K, div_eq_mul_inv] <;> ring
  have hi := c17_gaussian_dominated_second_moment_integrable d (C*t)⁻¹ K B
    (inv_pos.mpr hCt) hK hB.le x k ρ hk hρ hkb' hρb
  have hg : Integrable (fun y : Vec d =>
      (K*B) * (Real.exp (-euclideanSq (y-x)/(C*t)) * euclideanSq (y-x))) := by
    have h := (c17_shifted_gaussian_second_moment_integrable d (C*t)⁻¹
      (inv_pos.mpr hCt) x).const_mul (K*B)
    convert h using 1 <;> ext y <;> congr 3 <;> rw [div_eq_mul_inv] <;> ring
  have hb : (∫ y, k y * euclideanSq (y-x) * ρ y) ≤
      (∫ y : Vec d, (K*B) * (Real.exp (-euclideanSq (y-x)/(C*t)) * euclideanSq (y-x))) := by
    apply integral_mono hi hg
    intro y
    have hs : 0 ≤ euclideanSq (y-x) := by
      simp only [euclideanSq, dot]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have he := (Real.exp_pos (-euclideanSq (y-x)/(C*t))).le
    calc
      _ ≤ (K * Real.exp (-euclideanSq (y-x)/(C*t))) * euclideanSq (y-x) * B :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hkb y).2 hs) (hρb y).2
          (hρb y).1 (mul_nonneg (mul_nonneg hK he) hs)
      _ = _ := by ring
  rw [integral_const_mul, c17_gaussian_second_moment_formula d (C*t) hCt x] at hb
  have halg : K * Real.rpow (C*t) ((d : ℝ)/2+1) =
      Real.rpow C ((d : ℝ)/2+2) * t := c17_gaussian_scale_algebra d C t hC ht
  have hpos : 0 ≤ B * (Real.rpow C ((d : ℝ)/2+2) * t) :=
    mul_nonneg hB.le (mul_nonneg (Real.rpow_nonneg hC.le _) ht.le)
  calc
    _ ≤ (K*B) * (Real.rpow (C*t) ((d : ℝ)/2+1) * S) := hb
    _ = S * (B * (Real.rpow C ((d : ℝ)/2+2) * t)) := by rw [← halg]; ring
    _ ≤ (S+1) * (B * (Real.rpow C ((d : ℝ)/2+2) * t)) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos
    _ = _ := by ring

/-- Moment control for the zero-extended native spectral series, under an
explicit Gaussian estimate and measurability of that representative. -/
theorem c17_native_spectral_row_second_moment (d : ℕ) (hd : 2 ≤ d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (κ R : ℝ) (hκ : 0 < κ)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
      (s : EinsteinFull.External.Source.GMP.DirichletSpectralResolution ρ α R)
      (C t : ℝ), 0 < C → 0 < t → ∀ x : Vec d,
      let k := (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R).indicator
        (fun y => ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
      Measurable k →
      (∀ y, 0 ≤ k y ∧ k y ≤ C * Real.rpow t (-(d : ℝ)/2) *
        Real.exp (-euclideanSq (y-x)/(C*t))) →
      Integrable (fun y => k y * euclideanSq (y-x) * ρ y) ∧
      (∫ y, k y * euclideanSq (y-x) * ρ y) ≤
        D * κ⁻¹ * Real.rpow C ((d : ℝ)/2+2) * t := by
  obtain ⟨D, hD, hbound⟩ := c17_gaussian_kernel_second_moment d hd
  refine ⟨D, hD, ?_⟩
  intro κ R hκ ρ α h s C t hC ht x k hk hkb
  have hρb : ∀ y, 0 ≤ ρ y ∧ ρ y ≤ κ⁻¹ :=
    fun y => ⟨le_trans hκ.le (h.2.2 y).1, (h.2.2 y).2.1⟩
  constructor
  · apply c17_gaussian_dominated_second_moment_integrable d (C*t)⁻¹
      (C * Real.rpow t (-(d : ℝ)/2)) κ⁻¹
      (inv_pos.mpr (mul_pos hC ht))
      (mul_nonneg hC.le (Real.rpow_nonneg ht.le _)) (inv_nonneg.mpr hκ.le)
      x k ρ hk h.1 ?_ hρb
    intro y
    convert hkb y using 1 <;> simp only [div_eq_mul_inv] <;> ring
  · exact hbound ρ h.1 κ⁻¹ (inv_pos.mpr hκ) hρb C t hC ht x k hk hkb

end EinsteinFull.Calculus
