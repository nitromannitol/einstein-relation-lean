import EinsteinFull.Work.W4.MellinCutoffSupport
import EinsteinFull.Work.W3.GaussianTaylorSupport
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Exact Gaussian finite-part evaluation for `paper/main.tex`,
`e:even-finitepart` and `e:odd-finitepart`. The proofs retain the
Taylor-derivative coefficients and the literal `Ioo`/`Ioi` cutoffs. -/

open MeasureTheory Set Filter
open scoped Topology
open scoped BigOperators

namespace EinsteinFull

/-- Addition of signed amplitudes commutes with the derivative-defined coefficients. -/
theorem profileTaylorCoefficient_add (u₀ u₂ v₀ v₂ γ : ℝ) (j : ℕ) :
    profileTaylorCoefficient (u₀ + v₀) (u₂ + v₂) γ j =
      profileTaylorCoefficient u₀ u₂ γ j + profileTaylorCoefficient v₀ v₂ γ j := by
  simp only [profileTaylorCoefficient_eq]
  split_ifs <;> ring

/-- Scalar multiplication of signed amplitudes commutes with the Taylor coefficients. -/
theorem profileTaylorCoefficient_smul (a u₀ u₂ γ : ℝ) (j : ℕ) :
    profileTaylorCoefficient (a * u₀) (a * u₂) γ j =
      a * profileTaylorCoefficient u₀ u₂ γ j := by
  simp only [profileTaylorCoefficient_eq]
  split_ifs <;> ring

/-- Dilation acts on the literal coefficients by the degree of the derivative. -/
theorem profileTaylorCoefficient_dilate (a u₀ u₂ γ : ℝ) (j : ℕ) :
    profileTaylorCoefficient u₀ (u₂ * a ^ 2) (γ * a ^ 2) j =
      a ^ j * profileTaylorCoefficient u₀ u₂ γ j := by
  have he : gaussianProfile u₀ (u₂ * a ^ 2) (γ * a ^ 2) =
      fun u => gaussianProfile u₀ u₂ γ (a * u) := by
    funext u
    simp only [gaussianProfile]
    congr 2 <;> ring
  unfold profileTaylorCoefficient
  rw [he, iteratedDeriv_comp_const_mul (contDiff_gaussianProfile u₀ u₂ γ j)]
  simp only [mul_zero]
  ring

/-- The finite part is additive in the two signed amplitudes. -/
theorem profileFinitePart_add (d : ℕ) (u₀ u₂ v₀ v₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    profileFinitePart d (u₀ + v₀) (u₂ + v₂) γ hγ =
      profileFinitePart d u₀ u₂ γ hγ + profileFinitePart d v₀ v₂ γ hγ := by
  have he (u : ℝ) : gaussianProfile (u₀ + v₀) (u₂ + v₂) γ u =
      gaussianProfile u₀ u₂ γ u + gaussianProfile v₀ v₂ γ u := by
    simp only [gaussianProfile]
    ring
  have hr (u : ℝ) :
      (gaussianProfile (u₀ + v₀) (u₂ + v₂) γ u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient (u₀ + v₀) (u₂ + v₂) γ j.val * u ^ j.val) /
        u ^ (d + 1) =
      (gaussianProfile u₀ u₂ γ u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) / u ^ (d + 1) +
      (gaussianProfile v₀ v₂ γ u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient v₀ v₂ γ j.val * u ^ j.val) / u ^ (d + 1) := by
    simp only [he, profileTaylorCoefficient_add, add_mul, Finset.sum_add_distrib]
    ring
  unfold profileFinitePart
  simp_rw [hr, he, profileTaylorCoefficient_add, add_div, Finset.sum_add_distrib]
  rw [integral_add (integrableOn_gaussianProfile_sub_taylor_div_pow_Ioo d u₀ u₂ γ)
    (integrableOn_gaussianProfile_sub_taylor_div_pow_Ioo d v₀ v₂ γ),
    integral_add (integrableOn_gaussianProfile_div_pow_Ioi_one d u₀ u₂ hγ)
      (integrableOn_gaussianProfile_div_pow_Ioi_one d v₀ v₂ hγ)]
  ring

/-- The finite part is homogeneous for every real, possibly negative, amplitude. -/
theorem profileFinitePart_smul (d : ℕ) (a u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    profileFinitePart d (a * u₀) (a * u₂) γ hγ =
      a * profileFinitePart d u₀ u₂ γ hγ := by
  have he (u : ℝ) : gaussianProfile (a * u₀) (a * u₂) γ u =
      a * gaussianProfile u₀ u₂ γ u := by simp only [gaussianProfile]; ring
  unfold profileFinitePart
  simp_rw [he, profileTaylorCoefficient_smul, mul_assoc, ← Finset.mul_sum,
    ← mul_sub, mul_div_assoc, integral_const_mul]
  simp only [← Finset.mul_sum]
  ring

/-- Reduction to the two actual Gaussian amplitude basis profiles. -/
theorem profileFinitePart_eq_amplitudes (d : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    profileFinitePart d u₀ u₂ γ hγ =
      u₀ * profileFinitePart d 1 0 γ hγ + u₂ * profileFinitePart d 0 1 γ hγ := by
  have h := profileFinitePart_add d (u₀ * 1) (u₀ * 0) (u₂ * 0) (u₂ * 1) hγ
  rw [profileFinitePart_smul, profileFinitePart_smul] at h
  simpa only [mul_one, mul_zero, add_zero, zero_add] using h

private theorem integral_comp_mul_Ioo (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioo (0 : ℝ) 1, f (a * u)) = a⁻¹ * ∫ u in Ioo (0 : ℝ) a, f u := by
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo,
    ← abs_of_pos (inv_pos.mpr ha)]
  change _ = |a⁻¹| • (∫ x : ℝ, (Ioo (0 : ℝ) a).indicator f x)
  rw [← Measure.integral_comp_mul_left]
  congr 1
  funext u
  have hpre : HMul.hMul a ⁻¹' Ioo (0 : ℝ) a = Ioo 0 1 := by
    have h := preimage_const_mul_Ioo₀ (0 : ℝ) a ha
    rw [zero_div, div_self ha.ne'] at h
    exact h
  rw [← indicator_comp_right, hpre]
  simp only [Function.comp_def]

private theorem profileFinitePart_dilate_le_one (d : ℕ) (u₀ u₂ : ℝ) {γ a : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    profileFinitePart d u₀ (u₂ * a ^ 2) (γ * a ^ 2) (by positivity) =
      a ^ d * (profileFinitePart d u₀ u₂ γ hγ -
        profileTaylorCoefficient u₀ u₂ γ d * Real.log a) := by
  let R : ℝ → ℝ := fun u =>
    (gaussianProfile u₀ u₂ γ u -
      ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) / u ^ (d + 1)
  let T : ℝ → ℝ := fun u => gaussianProfile u₀ u₂ γ u / u ^ (d + 1)
  have he (u : ℝ) : gaussianProfile u₀ (u₂ * a ^ 2) (γ * a ^ 2) u =
      gaussianProfile u₀ u₂ γ (a * u) := by
    simp only [gaussianProfile]
    congr 2 <;> ring
  have hp (u : ℝ) :
      (∑ j : Fin (d + 1), profileTaylorCoefficient u₀ (u₂ * a ^ 2) (γ * a ^ 2) j.val * u ^ j.val) =
      ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * (a * u) ^ j.val := by
    apply Finset.sum_congr rfl
    intro j _
    rw [profileTaylorCoefficient_dilate, mul_pow]
    ring
  have hr (u : ℝ) :
      (gaussianProfile u₀ (u₂ * a ^ 2) (γ * a ^ 2) u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ (u₂ * a ^ 2) (γ * a ^ 2) j.val * u ^ j.val) /
        u ^ (d + 1) = a ^ (d + 1) * R (a * u) := by
    rw [he, hp]
    dsimp only [R]
    rw [mul_pow]
    field_simp
  have ht (u : ℝ) : gaussianProfile u₀ (u₂ * a ^ 2) (γ * a ^ 2) u / u ^ (d + 1) =
      a ^ (d + 1) * T (a * u) := by
    rw [he]
    dsimp only [T]
    rw [mul_pow]
    field_simp
  have hmon (j : Fin d) :
      a ^ d * (profileTaylorCoefficient u₀ u₂ γ j.val /
        ((d - j.val : ℕ) : ℝ) * (1 / a ^ (d - j.val))) =
      profileTaylorCoefficient u₀ (u₂ * a ^ 2) (γ * a ^ 2) j.val /
        ((d - j.val : ℕ) : ℝ) := by
    rw [profileTaylorCoefficient_dilate,
      show a ^ d = a ^ j.val * a ^ (d - j.val) by
        rw [← pow_add, Nat.add_sub_of_le j.isLt.le]]
    field_simp
  have hc := gaussianProfile_mellin_cutoff_unscaled ha ha₁ d u₀ u₂ hγ
  change (∫ u in Ioi a, T u) = _ + _ + _ - ∫ u in Ioo 0 a, R u at hc
  unfold profileFinitePart
  simp_rw [hr, ht]
  rw [integral_const_mul, integral_comp_mul_Ioo R ha,
    integral_const_mul, integral_comp_mul_left_Ioi T 1 ha]
  simp only [smul_eq_mul, mul_one]
  rw [show a ^ (d + 1) * (a⁻¹ * ∫ u in Ioo (0 : ℝ) a, R u) =
      a ^ d * ∫ u in Ioo (0 : ℝ) a, R u by rw [pow_succ]; field_simp,
    show a ^ (d + 1) * (a⁻¹ * ∫ u in Ioi a, T u) =
      a ^ d * ∫ u in Ioi a, T u by rw [pow_succ]; field_simp, hc]
  rw [Real.log_div one_ne_zero ha.ne', Real.log_one, zero_sub]
  simp_rw [mul_sub, mul_add, Finset.mul_sum, hmon]
  rw [profileFinitePart]
  simp_rw [mul_sub, mul_add, Finset.mul_sum]
  dsimp only [R, T]
  ring

/-- Exact dilation of the manuscript finite part, including its critical logarithm.
The formula holds for every natural order, hence in particular for `d ≥ 2`. -/
theorem profileFinitePart_dilate (d : ℕ) (u₀ u₂ : ℝ) {γ a : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) :
    profileFinitePart d u₀ (u₂ * a ^ 2) (γ * a ^ 2) (by positivity) =
      a ^ d * (profileFinitePart d u₀ u₂ γ hγ -
        profileTaylorCoefficient u₀ u₂ γ d * Real.log a) := by
  by_cases ha₁ : a ≤ 1
  · exact profileFinitePart_dilate_le_one d u₀ u₂ hγ ha ha₁
  have h := profileFinitePart_dilate_le_one d u₀ (u₂ * a ^ 2)
    (mul_pos hγ (pow_pos ha 2)) (inv_pos.mpr ha)
    (inv_le_one_of_one_le₀ (le_of_not_ge ha₁))
  have he (b : ℝ) : b * a ^ 2 * a⁻¹ ^ 2 = b := by field_simp
  simp only [he, profileTaylorCoefficient_dilate, Real.log_inv] at h
  simp only [inv_pow, ← div_eq_inv_mul] at h
  have ha₀ : a ^ d ≠ 0 := pow_ne_zero d ha.ne'
  apply (eq_div_iff ha₀).mp at h
  nlinarith only [h]

/-- Scaling the Gaussian rate from one retains precisely the Taylor logarithm.
Both amplitudes remain signed. -/
theorem profileFinitePart_rate (d : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    profileFinitePart d u₀ u₂ γ hγ =
      (Real.sqrt γ) ^ d * profileFinitePart d u₀ (u₂ / γ) 1 zero_lt_one -
        profileTaylorCoefficient u₀ u₂ γ d * (Real.log γ / 2) := by
  have ha : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have he : (Real.sqrt γ) ^ 2 = γ := Real.sq_sqrt hγ.le
  have hc := profileTaylorCoefficient_dilate (Real.sqrt γ) u₀ (u₂ / γ) 1 d
  have hm := profileFinitePart_dilate d u₀ (u₂ / γ) zero_lt_one ha
  have he₂ : u₂ / γ * γ = u₂ := div_mul_cancel₀ u₂ hγ.ne'
  simp only [he, one_mul, he₂] at hc hm
  rw [hm, mul_sub, ← mul_assoc, ← hc, Real.log_sqrt hγ.le]

/-- At odd orders the critical coefficient vanishes, so rate scaling has no log term. -/
theorem profileFinitePart_rate_odd (n : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    profileFinitePart (2 * n + 1) u₀ u₂ γ hγ =
      (Real.sqrt γ) ^ (2 * n + 1) *
        profileFinitePart (2 * n + 1) u₀ (u₂ / γ) 1 zero_lt_one := by
  rw [profileFinitePart_rate, profileTaylorCoefficient_odd, zero_mul, sub_zero]

/-- Multiplication by `u²` shifts the actual derivative-defined coefficients. -/
theorem profileTaylorCoefficient_quadratic (γ : ℝ) (j : ℕ) :
    profileTaylorCoefficient 0 1 γ (j + 2) = profileTaylorCoefficient 1 0 γ j := by
  have hm : (j + 2) % 2 = j % 2 := by omega
  have hd : (j + 2) / 2 = j / 2 + 1 := by omega
  simp [profileTaylorCoefficient_eq, hm, hd]

/-- The quadratic-amplitude finite part is exactly the pure Gaussian finite part
at order two lower, with the same subtraction convention. -/
theorem profileFinitePart_quadratic (d : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    profileFinitePart (d + 2) 0 1 γ hγ = profileFinitePart d 1 0 γ hγ := by
  have he (u : ℝ) : gaussianProfile 0 1 γ u = u ^ 2 * gaussianProfile 1 0 γ u := by
    simp only [gaussianProfile, zero_add, one_mul, zero_mul, add_zero]
  have hp (u : ℝ) :
      (∑ j : Fin (d + 2 + 1), profileTaylorCoefficient 0 1 γ j.val * u ^ j.val) =
      u ^ 2 * ∑ j : Fin (d + 1), profileTaylorCoefficient 1 0 γ j.val * u ^ j.val := by
    rw [show d + 2 + 1 = (d + 1) + 1 + 1 by omega,
      Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, profileTaylorCoefficient_zero,
      show profileTaylorCoefficient 0 1 γ 1 = 0 by
        simpa only [zero_mul, zero_add] using profileTaylorCoefficient_odd 0 1 γ 0,
      zero_mul, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [profileTaylorCoefficient_quadratic, pow_add]
    ring
  have hr (u : ℝ) :
      (gaussianProfile 0 1 γ u -
        ∑ j : Fin (d + 2 + 1), profileTaylorCoefficient 0 1 γ j.val * u ^ j.val) / u ^ (d + 2 + 1) =
      (gaussianProfile 1 0 γ u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient 1 0 γ j.val * u ^ j.val) / u ^ (d + 1) := by
    by_cases hu : u = 0
    · simp [hu]
    rw [he, hp, ← mul_sub, show d + 2 + 1 = 2 + (d + 1) by omega, pow_add]
    field_simp
  have ht (u : ℝ) : gaussianProfile 0 1 γ u / u ^ (d + 2 + 1) =
      gaussianProfile 1 0 γ u / u ^ (d + 1) := by
    by_cases hu : u = 0
    · simp [hu]
    rw [he, show d + 2 + 1 = 2 + (d + 1) by omega, pow_add]
    field_simp
  unfold profileFinitePart
  simp_rw [hr, ht]
  congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, profileTaylorCoefficient_zero,
    show profileTaylorCoefficient 0 1 γ 1 = 0 by
      simpa only [zero_mul, zero_add] using profileTaylorCoefficient_odd 0 1 γ 0,
    zero_div, zero_add, profileTaylorCoefficient_quadratic]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  omega

/-- For source dimensions `d ≥ 2`, only pure Gaussian finite parts remain to evaluate. -/
theorem profileFinitePart_eq_pure (d : ℕ) (hd : 2 ≤ d) (u₀ u₂ : ℝ)
    {γ : ℝ} (hγ : 0 < γ) :
    profileFinitePart d u₀ u₂ γ hγ =
      u₀ * profileFinitePart d 1 0 γ hγ + u₂ * profileFinitePart (d - 2) 1 0 γ hγ := by
  rw [profileFinitePart_eq_amplitudes,
    show d = (d - 2) + 2 by omega, profileFinitePart_quadratic]
  simp only [Nat.add_sub_cancel]

/-- The actual pure-Gaussian coefficients obey the two-step differential recurrence. -/
theorem profileTaylorCoefficient_pure_step (γ : ℝ) (j : ℕ) :
    (j + 2 : ℝ) * profileTaylorCoefficient 1 0 γ (j + 2) =
      -2 * γ * profileTaylorCoefficient 1 0 γ j := by
  have he (n : ℕ) : profileTaylorCoefficient 1 0 γ (2 * n) =
      (-γ) ^ n / (n.factorial : ℝ) := by
    simp [profileTaylorCoefficient_even]
  by_cases hj : j % 2 = 0
  · have hj' : j = 2 * (j / 2) := by omega
    rw [hj', show 2 * (j / 2) + 2 = 2 * (j / 2 + 1) by omega, he, he,
      Nat.factorial_succ, pow_succ]
    push_cast
    have hn : ((j / 2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j / 2)
    have hn₁ : ((j / 2 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · have hj' : j = 2 * (j / 2) + 1 := by omega
    rw [hj', show 2 * (j / 2) + 1 + 2 = 2 * (j / 2 + 1) + 1 by omega,
      profileTaylorCoefficient_odd, profileTaylorCoefficient_odd]
    ring

private noncomputable def pureTaylor (d : ℕ) (γ u : ℝ) : ℝ :=
  ∑ j : Fin (d + 1), profileTaylorCoefficient 1 0 γ j.val * u ^ j.val

private theorem hasDerivAt_pureTaylor (d : ℕ) (γ u : ℝ) :
    HasDerivAt (pureTaylor (d + 2) γ) (-2 * γ * u * pureTaylor d γ u) u := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin (d + 2 + 1)))) =>
    ((hasDerivAt_id u).pow j.val).const_mul (profileTaylorCoefficient 1 0 γ j.val))
  change HasDerivAt (pureTaylor (d + 2) γ)
    (∑ j : Fin (d + 2 + 1), profileTaylorCoefficient 1 0 γ j.val *
      ((j.val : ℝ) * u ^ (j.val - 1) * 1)) u at h
  convert h using 1
  rw [show d + 2 + 1 = (d + 1) + 1 + 1 by omega,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, zero_mul, mul_zero,
    profileTaylorCoefficient_odd 1 0 γ 0, zero_add, Nat.add_sub_cancel,
    mul_one, Nat.cast_add, Nat.cast_one]
  unfold pureTaylor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hc := profileTaylorCoefficient_pure_step γ j.val
  rw [pow_succ]
  push_cast at hc
  linear_combination -(u ^ j.val * u) * hc

private noncomputable def pureRemainder (d : ℕ) (γ u : ℝ) : ℝ :=
  (gaussianProfile 1 0 γ u - pureTaylor d γ u) / u ^ (d + 1)

private noncomputable def purePrimitive (d : ℕ) (γ u : ℝ) : ℝ :=
  (gaussianProfile 1 0 γ u - pureTaylor d γ u) / u ^ d

private theorem hasDerivAt_pureGaussian (γ u : ℝ) :
    HasDerivAt (gaussianProfile 1 0 γ) (-2 * γ * u * gaussianProfile 1 0 γ u) u := by
  have h := (((hasDerivAt_id u).pow 2).const_mul (-γ)).exp
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at h
  have he : gaussianProfile 1 0 γ = fun x => Real.exp (-γ * x ^ 2) := by
    funext x
    simp only [gaussianProfile, zero_mul, add_zero, one_mul]
  rw [he]
  convert h using 1
  ring

private theorem hasDerivAt_purePrimitive (d : ℕ) (γ : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (purePrimitive (d + 2) γ)
      (-(d + 2 : ℝ) * pureRemainder (d + 2) γ u - 2 * γ * pureRemainder d γ u) u := by
  have h := ((hasDerivAt_pureGaussian γ u).sub (hasDerivAt_pureTaylor d γ u)).div
    ((hasDerivAt_id u).pow (d + 2)) (pow_ne_zero _ hu)
  have h' : HasDerivAt (purePrimitive (d + 2) γ)
      (((-2 * γ * u * gaussianProfile 1 0 γ u - (-2 * γ * u * pureTaylor d γ u)) * u ^ (d + 2) -
        (gaussianProfile 1 0 γ u - pureTaylor (d + 2) γ u) *
          (((d + 2 : ℕ) : ℝ) * u ^ (d + 1) * 1)) / (u ^ (d + 2)) ^ 2) u := h
  refine h'.congr_deriv ?_
  simp only [pureRemainder]
  push_cast
  field_simp
  ring

private theorem tendsto_purePrimitive_zero (d : ℕ) (γ : ℝ) :
    Tendsto (purePrimitive d γ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_gaussianProfile_sub_taylor_div_pow_bound d 1 0 γ
  apply squeeze_zero_norm' (a := fun u : ℝ => C * u)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    have he : purePrimitive d γ u = u * pureRemainder d γ u := by
      dsimp only [purePrimitive, pureRemainder]
      rw [pow_succ]
      field_simp [hu.1.ne']
    rw [he, norm_mul, Real.norm_eq_abs, abs_of_pos hu.1]
    exact (mul_le_mul_of_nonneg_left (hC u hu) hu.1.le).trans_eq (mul_comm _ _)
  · simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) :
        Tendsto (fun u : ℝ => C * u) (𝓝[>] 0) (𝓝 (C * 0)))

private theorem integral_pureRemainder_parts (d : ℕ) (γ : ℝ) :
    -(d + 2 : ℝ) * (∫ u in Ioo (0 : ℝ) 1, pureRemainder (d + 2) γ u) -
      2 * γ * (∫ u in Ioo (0 : ℝ) 1, pureRemainder d γ u) =
      gaussianProfile 1 0 γ 1 - pureTaylor (d + 2) γ 1 := by
  have hq : IntegrableOn (pureRemainder (d + 2) γ) (Ioo 0 1) :=
    integrableOn_gaussianProfile_sub_taylor_div_pow_Ioo (d + 2) 1 0 γ
  have hd : IntegrableOn (pureRemainder d γ) (Ioo 0 1) :=
    integrableOn_gaussianProfile_sub_taylor_div_pow_Ioo d 1 0 γ
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u (hu : u ∈ Ioo (0 : ℝ) 1) => hasDerivAt_purePrimitive d γ hu.1.ne')
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      ((hq.const_mul _).sub (hd.const_mul _)))
    (tendsto_purePrimitive_zero (d + 2) γ)
    ((hasDerivAt_purePrimitive d γ one_ne_zero).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_sub (hq.const_mul _) (hd.const_mul _), integral_const_mul,
    integral_const_mul] at hi
  simpa only [purePrimitive, one_pow, div_one, sub_zero] using hi

private theorem hasDerivAt_pureTail (d : ℕ) (γ : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun x => gaussianProfile 1 0 γ x / x ^ (d + 2))
      (-(d + 2 : ℝ) * (gaussianProfile 1 0 γ u / u ^ (d + 2 + 1)) -
        2 * γ * (gaussianProfile 1 0 γ u / u ^ (d + 1))) u := by
  have h := (hasDerivAt_pureGaussian γ u).div
    ((hasDerivAt_id u).pow (d + 2)) (pow_ne_zero _ hu)
  have h' : HasDerivAt (fun x => gaussianProfile 1 0 γ x / x ^ (d + 2))
      ((-2 * γ * u * gaussianProfile 1 0 γ u * u ^ (d + 2) -
        gaussianProfile 1 0 γ u * (((d + 2 : ℕ) : ℝ) * u ^ (d + 1) * 1)) /
          (u ^ (d + 2)) ^ 2) u := h
  refine h'.congr_deriv ?_
  push_cast
  field_simp
  ring

private theorem integral_pureTail_parts (d : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    -(d + 2 : ℝ) * (∫ u in Ioi (1 : ℝ), gaussianProfile 1 0 γ u / u ^ (d + 2 + 1)) -
      2 * γ * (∫ u in Ioi (1 : ℝ), gaussianProfile 1 0 γ u / u ^ (d + 1)) =
      -gaussianProfile 1 0 γ 1 := by
  have hq := integrableOn_gaussianProfile_div_pow_Ioi_one (d + 2) 1 0 hγ
  have hd := integrableOn_gaussianProfile_div_pow_Ioi_one d 1 0 hγ
  have ht : Tendsto (fun u => gaussianProfile 1 0 γ u / u ^ (d + 2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun u : ℝ => (u ^ (d + 2))⁻¹)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have he : 0 < gaussianProfile 1 0 γ u := by simp only [gaussianProfile]; positivity
      have he₁ : gaussianProfile 1 0 γ u ≤ 1 := by
        simp only [gaussianProfile, zero_mul, add_zero, one_mul, Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg u)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg he.le (pow_pos hu _).le), ← one_div]
      exact div_le_div_of_nonneg_right he₁ (pow_pos hu _).le
    · exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega))
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u (hu : u ∈ Ici (1 : ℝ)) => hasDerivAt_pureTail d γ (ne_of_gt (zero_lt_one.trans_le hu)))
    ((hq.const_mul _).sub (hd.const_mul _)) ht
  rw [integral_sub (hq.const_mul _) (hd.const_mul _), integral_const_mul,
    integral_const_mul] at hi
  simpa only [one_pow, div_one, zero_sub] using hi

private theorem pureTaylor_sum_parts (d : ℕ) (γ : ℝ) :
    (d + 2 : ℝ) * (∑ j : Fin (d + 2),
      profileTaylorCoefficient 1 0 γ j.val / ((d + 2 - j.val : ℕ) : ℝ)) +
    2 * γ * (∑ j : Fin d,
      profileTaylorCoefficient 1 0 γ j.val / ((d - j.val : ℕ) : ℝ)) =
    pureTaylor (d + 2) γ 1 - profileTaylorCoefficient 1 0 γ (d + 2) := by
  have hq : (d + 2 : ℝ) ≠ 0 := by positivity
  have hsum : pureTaylor (d + 2) γ 1 - profileTaylorCoefficient 1 0 γ (d + 2) =
      ∑ j : Fin (d + 2), profileTaylorCoefficient 1 0 γ j.val := by
    simp only [pureTaylor, one_pow, mul_one, Fin.sum_univ_castSucc, Fin.val_castSucc,
      Fin.val_last, add_sub_cancel_right]
  rw [hsum]
  have hshift :
      (∑ j : Fin (d + 2), profileTaylorCoefficient 1 0 γ j.val / ((d + 2 - j.val : ℕ) : ℝ)) =
      1 / (d + 2 : ℝ) +
        ∑ j : Fin d, profileTaylorCoefficient 1 0 γ (j.val + 2) / ((d - j.val : ℕ) : ℝ) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, profileTaylorCoefficient_zero,
      show profileTaylorCoefficient 1 0 γ 1 = 0 by
        simpa only [zero_mul, zero_add] using profileTaylorCoefficient_odd 1 0 γ 0,
      zero_div, zero_add, Nat.sub_zero, Nat.cast_add, Nat.cast_ofNat]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega
  have hshift' : (∑ j : Fin (d + 2), profileTaylorCoefficient 1 0 γ j.val) =
      1 + ∑ j : Fin d, profileTaylorCoefficient 1 0 γ (j.val + 2) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, profileTaylorCoefficient_zero,
      show profileTaylorCoefficient 1 0 γ 1 = 0 by
        simpa only [zero_mul, zero_add] using profileTaylorCoefficient_odd 1 0 γ 0,
      zero_add, Nat.add_assoc]
  rw [hshift, hshift', mul_add, mul_one_div_cancel hq, Finset.mul_sum,
    Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hc := profileTaylorCoefficient_pure_step γ j.val
  have hd : ((d - j.val : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt j.isLt)
  have he : ((d - j.val : ℕ) : ℝ) = (d : ℝ) - (j.val : ℝ) :=
    Nat.cast_sub j.isLt.le
  rw [he]
  rw [he] at hd
  field_simp
  push_cast at hc
  linear_combination hc

/-- Integration by parts for the literal pure-Gaussian finite part. The critical
Taylor coefficient supplies the additive correction at even orders. -/
theorem profileFinitePart_pure_recurrence (d : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    (d + 2 : ℝ) * profileFinitePart (d + 2) 1 0 γ hγ =
      -2 * γ * profileFinitePart d 1 0 γ hγ + profileTaylorCoefficient 1 0 γ (d + 2) := by
  have hsmall := integral_pureRemainder_parts d γ
  have htail := integral_pureTail_parts d hγ
  have hsum := pureTaylor_sum_parts d γ
  unfold profileFinitePart
  change -(d + 2 : ℝ) * (∫ u in Ioo (0 : ℝ) 1,
      (gaussianProfile 1 0 γ u - pureTaylor (d + 2) γ u) / u ^ (d + 2 + 1)) -
      2 * γ * (∫ u in Ioo (0 : ℝ) 1,
        (gaussianProfile 1 0 γ u - pureTaylor d γ u) / u ^ (d + 1)) = _ at hsmall
  dsimp only [pureTaylor] at hsmall hsum
  linear_combination -hsmall - htail - hsum

/-- Exact harmonic-number evaluation in terms of the single literal order-zero
base integral. No value for that base is assumed. -/
theorem profileFinitePart_pure_even_base (n : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    2 * profileFinitePart (2 * n) 1 0 γ hγ =
      ((-γ) ^ n / (n.factorial : ℝ)) *
        (2 * profileFinitePart 0 1 0 γ hγ + (harmonic n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hr := profileFinitePart_pure_recurrence (2 * n) hγ
      rw [show 2 * n + 2 = 2 * (n + 1) by omega] at hr
      have hc : profileTaylorCoefficient 1 0 γ (2 * (n + 1)) =
          (-γ) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        simp [profileTaylorCoefficient_even]
      rw [hc] at hr
      have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      have hn₁ : (n : ℝ) + 1 ≠ 0 := by positivity
      apply mul_left_cancel₀ hn₁
      calc
        ((n : ℝ) + 1) * (2 * profileFinitePart (2 * (n + 1)) 1 0 γ hγ) =
            -γ * (2 * profileFinitePart (2 * n) 1 0 γ hγ) +
              (-γ) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          push_cast at hr
          linear_combination hr
        _ = _ := by
          rw [ih, harmonic_succ, Nat.factorial_succ, pow_succ]
          push_cast
          field_simp
          ring

/-- The even formula with the exact rate logarithm and only the order-zero
unit-rate finite part still unevaluated. -/
theorem profileFinitePart_pure_even_unit_base (n : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    2 * profileFinitePart (2 * n) 1 0 γ hγ =
      ((-γ) ^ n / (n.factorial : ℝ)) *
        (2 * profileFinitePart 0 1 0 1 zero_lt_one + (harmonic n : ℝ) - Real.log γ) := by
  have hbase := profileFinitePart_rate 0 1 0 hγ
  simp only [pow_zero, one_mul, zero_div, profileTaylorCoefficient_zero] at hbase
  rw [profileFinitePart_pure_even_base, hbase]
  ring

private theorem pureTaylor_one (γ u : ℝ) : pureTaylor 1 γ u = 1 := by
  unfold pureTaylor
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, profileTaylorCoefficient_zero,
    show profileTaylorCoefficient 1 0 γ 1 = 0 by
      simpa only [zero_mul, zero_add] using profileTaylorCoefficient_odd 1 0 γ 0,
    pow_zero, mul_one, zero_mul, Fin.sum_univ_zero, add_zero]

private theorem hasDerivAt_purePrimitive_one (γ : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (purePrimitive 1 γ)
      (-pureRemainder 1 γ u - 2 * γ * gaussianProfile 1 0 γ u) u := by
  have h := ((hasDerivAt_pureGaussian γ u).sub_const 1).div (hasDerivAt_id u) hu
  have he : purePrimitive 1 γ = fun x => (gaussianProfile 1 0 γ x - 1) / x := by
    funext x
    simp only [purePrimitive, pureTaylor_one, pow_one]
  have h' : HasDerivAt (fun x => (gaussianProfile 1 0 γ x - 1) / x)
      ((-2 * γ * u * gaussianProfile 1 0 γ u * u - (gaussianProfile 1 0 γ u - 1) * 1) / u ^ 2) u := h
  rw [he]
  refine h'.congr_deriv ?_
  simp only [pureRemainder, pureTaylor_one]
  field_simp
  ring

private theorem hasDerivAt_pureTail_one (γ : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun x => gaussianProfile 1 0 γ x / x)
      (-(gaussianProfile 1 0 γ u / u ^ 2) - 2 * γ * gaussianProfile 1 0 γ u) u := by
  have h := (hasDerivAt_pureGaussian γ u).div (hasDerivAt_id u) hu
  have h' : HasDerivAt (fun x => gaussianProfile 1 0 γ x / x)
      ((-2 * γ * u * gaussianProfile 1 0 γ u * u - gaussianProfile 1 0 γ u * 1) / u ^ 2) u := h
  refine h'.congr_deriv ?_
  field_simp
  ring

/-- The odd base finite part is evaluated by the ordinary half-line Gaussian integral. -/
theorem profileFinitePart_pure_one {γ : ℝ} (hγ : 0 < γ) :
    profileFinitePart 1 1 0 γ hγ = -γ * Real.sqrt (Real.pi / γ) := by
  have hR : IntegrableOn (pureRemainder 1 γ) (Ioo 0 1) :=
    integrableOn_gaussianProfile_sub_taylor_div_pow_Ioo 1 1 0 γ
  have hH := integrable_gaussianProfile 1 0 hγ
  have hs := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u (hu : u ∈ Ioo (0 : ℝ) 1) => hasDerivAt_purePrimitive_one γ hu.1.ne')
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (hR.neg.sub (hH.integrableOn.const_mul _)))
    (tendsto_purePrimitive_zero 1 γ)
    ((hasDerivAt_purePrimitive_one γ one_ne_zero).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  change (∫ u in (0 : ℝ)..1, (-pureRemainder 1 γ) u -
    (2 * γ) * gaussianProfile 1 0 γ u) = _ at hs
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_sub hR.neg (hH.integrableOn.const_mul _)] at hs
  simp only [Pi.neg_apply, integral_neg, integral_const_mul] at hs
  simp only [purePrimitive, pureTaylor_one, one_pow, div_one, sub_zero] at hs
  have htend : Tendsto (fun u => gaussianProfile 1 0 γ u / u) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun u : ℝ => u⁻¹)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have he : 0 < gaussianProfile 1 0 γ u := by simp only [gaussianProfile]; positivity
      have he₁ : gaussianProfile 1 0 γ u ≤ 1 := by
        simp only [gaussianProfile, zero_mul, add_zero, one_mul, Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg u)
      rw [Real.norm_eq_abs, abs_of_pos (div_pos he hu), ← one_div]
      exact div_le_div_of_nonneg_right he₁ hu.le
    · exact tendsto_inv_atTop_zero
  have hT := integrableOn_gaussianProfile_div_pow_Ioi_one 1 1 0 hγ
  have ht := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u (hu : u ∈ Ici (1 : ℝ)) => hasDerivAt_pureTail_one γ (ne_of_gt (zero_lt_one.trans_le hu)))
    (hT.neg.sub (hH.integrableOn.const_mul _)) htend
  change (∫ u in Ioi (1 : ℝ), (-(fun x => gaussianProfile 1 0 γ x / x ^ 2)) u -
    (2 * γ) * gaussianProfile 1 0 γ u) = _ at ht
  rw [integral_sub hT.neg (hH.integrableOn.const_mul _)] at ht
  simp only [Pi.neg_apply, integral_neg, integral_const_mul] at ht
  simp only [div_one, zero_sub] at ht
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
    measurableSet_Ioi (hH.integrableOn (s := Ioc 0 1)) (hH.integrableOn (s := Ioi 1))
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one, integral_Ioc_eq_integral_Ioo] at hsplit
  have hgauss : (∫ u in Ioi (0 : ℝ), gaussianProfile 1 0 γ u) = Real.sqrt (Real.pi / γ) / 2 := by
    simpa only [gaussianProfile, zero_mul, add_zero, one_mul] using integral_gaussian_Ioi γ
  unfold profileFinitePart
  change -(∫ u in Ioo (0 : ℝ) 1,
      (gaussianProfile 1 0 γ u - pureTaylor 1 γ u) / u ^ 2) -
      2 * γ * (∫ u in Ioo (0 : ℝ) 1, gaussianProfile 1 0 γ u) = _ at hs
  dsimp only [pureTaylor] at hs
  have hc0 : (∑ j : Fin 1, profileTaylorCoefficient 1 0 γ j.val /
      ((1 - j.val : ℕ) : ℝ)) = 1 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
      Nat.sub_zero, Nat.cast_one, profileTaylorCoefficient_zero, div_one, add_zero]
  rw [hc0]
  rw [hgauss] at hsplit
  linear_combination -hs - ht + 2 * γ * hsplit

/-- The full odd-order pure Gaussian finite part at unit rate. -/
theorem profileFinitePart_pure_odd_unit (n : ℕ) :
    2 * profileFinitePart (2 * n + 1) 1 0 1 zero_lt_one =
      Real.Gamma (-((2 * n + 1 : ℕ) : ℝ) / 2) := by
  induction n with
  | zero =>
      rw [profileFinitePart_pure_one]
      have hg := Real.Gamma_add_one (s := -(1 : ℝ) / 2) (by norm_num)
      norm_num only [neg_div, neg_add_cancel_right, show -(1 : ℝ) / 2 + 1 = 1 / 2 by norm_num] at hg
      rw [Real.Gamma_one_half_eq] at hg
      norm_num only [Nat.mul_zero, zero_add, Nat.cast_one, div_one, neg_mul, one_mul]
      linarith only [hg]
  | succ n ih =>
      have hr := profileFinitePart_pure_recurrence (2 * n + 1) zero_lt_one
      rw [show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by omega,
        profileTaylorCoefficient_odd] at hr
      have hs : -((2 * (n + 1) + 1 : ℕ) : ℝ) / 2 ≠ 0 :=
        div_ne_zero (neg_ne_zero.mpr (by positivity)) (by norm_num)
      have hg := Real.Gamma_add_one hs
      have he : -((2 * (n + 1) + 1 : ℕ) : ℝ) / 2 + 1 =
          -((2 * n + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
      rw [he] at hg
      push_cast at ih hr hg ⊢
      have hn : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      linear_combination 2 * hr - 2 * ih - 2 * hg

/-- Exact odd-order Gamma evaluation with the Gaussian rate kept positive. -/
theorem profileFinitePart_pure_odd (n : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    2 * profileFinitePart (2 * n + 1) 1 0 γ hγ =
      γ ^ (((2 * n + 1 : ℕ) : ℝ) / 2) *
        Real.Gamma (-((2 * n + 1 : ℕ) : ℝ) / 2) := by
  rw [profileFinitePart_rate_odd]
  simp only [zero_div]
  rw [show 2 * ((Real.sqrt γ) ^ (2 * n + 1) *
      profileFinitePart (2 * n + 1) 1 0 1 zero_lt_one) =
      (Real.sqrt γ) ^ (2 * n + 1) *
        (2 * profileFinitePart (2 * n + 1) 1 0 1 zero_lt_one) by ring,
    profileFinitePart_pure_odd_unit]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hγ.le]
  congr 1
  ring

/-- The manuscript odd Gamma formula, for every source dimension `d ≥ 2` that
is odd, expressed as `d = 2*n+3`. The normalization is exactly `2*M_d`. -/
theorem profileFinitePart_odd (n : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    2 * profileFinitePart (2 * n + 3) u₀ u₂ γ hγ =
      u₀ * γ ^ (((2 * n + 3 : ℕ) : ℝ) / 2) * Real.Gamma (-((2 * n + 3 : ℕ) : ℝ) / 2) +
      u₂ * γ ^ ((((2 * n + 3 : ℕ) : ℝ) - 2) / 2) *
        Real.Gamma (1 - ((2 * n + 3 : ℕ) : ℝ) / 2) := by
  rw [profileFinitePart_eq_pure _ (by omega), show 2 * n + 3 - 2 = 2 * n + 1 by omega]
  calc
    _ = u₀ * (2 * profileFinitePart (2 * n + 3) 1 0 γ hγ) +
        u₂ * (2 * profileFinitePart (2 * n + 1) 1 0 γ hγ) := by ring
    _ = _ := by
      rw [show 2 * n + 3 = 2 * (n + 1) + 1 by omega,
        profileFinitePart_pure_odd, profileFinitePart_pure_odd]
      have he : (((2 * (n + 1) + 1 : ℕ) : ℝ) - 2) / 2 = ((2 * n + 1 : ℕ) : ℝ) / 2 := by
        push_cast
        ring
      have hg : 1 - ((2 * (n + 1) + 1 : ℕ) : ℝ) / 2 = -((2 * n + 1 : ℕ) : ℝ) / 2 := by
        push_cast
        ring
      rw [he, hg]
      ring

/-- Reduction of the signed-amplitude even formula to its literal unit-rate base.
`profileFinitePart_pure_zero_unit` evaluates that base below. -/
theorem profileFinitePart_even_unit_base (n : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    2 * profileFinitePart (2 * (n + 1)) u₀ u₂ γ hγ =
      u₀ * ((-γ) ^ (n + 1) / ((n + 1).factorial : ℝ)) *
        (2 * profileFinitePart 0 1 0 1 zero_lt_one + (harmonic (n + 1) : ℝ) - Real.log γ) +
      u₂ * ((-γ) ^ n / (n.factorial : ℝ)) *
        (2 * profileFinitePart 0 1 0 1 zero_lt_one + (harmonic n : ℝ) - Real.log γ) := by
  rw [profileFinitePart_eq_pure _ (by omega), show 2 * (n + 1) - 2 = 2 * n by omega]
  calc
    _ = u₀ * (2 * profileFinitePart (2 * (n + 1)) 1 0 γ hγ) +
        u₂ * (2 * profileFinitePart (2 * n) 1 0 γ hγ) := by ring
    _ = _ := by rw [profileFinitePart_pure_even_unit_base, profileFinitePart_pure_even_unit_base]; ring

private theorem gamma_log_integral :
    IntegrableOn (fun y : ℝ => Real.log y * Real.exp (-y)) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), Real.log y * Real.exp (-y)) = -Real.eulerMascheroniConstant := by
  have hm := mellin_hasDerivAt_of_isBigO_rpow (E := ℂ)
    (a := (2 : ℝ)) (b := (0 : ℝ)) (s := (1 : ℂ))
    (f := fun y : ℝ => (Real.exp (-y) : ℂ))
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousOn.locallyIntegrableOn
      measurableSet_Ioi) (by
      rw [← Asymptotics.isBigO_norm_left]
      simp_rw [Complex.norm_real, Asymptotics.isBigO_norm_left]
      simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-2)).isBigO)
    (by norm_num) (by
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero,
        norm_one, mul_one, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy.le)) (by norm_num)
  have hi : IntegrableOn (fun y : ℝ => ((Real.log y * Real.exp (-y) : ℝ) : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul,
      Complex.real_smul, Complex.ofReal_mul] using hm.1
  have hr : IntegrableOn (fun y : ℝ => Real.log y * Real.exp (-y)) (Ioi 0) := by
    exact hi.re
  refine ⟨hr, ?_⟩
  have he : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
    filter_upwards [Complex.continuous_re.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num))] with z hz
    exact Complex.Gamma_eq_integral hz
  have hd := (Complex.hasDerivAt_GammaIntegral (s := 1) (by norm_num)).congr_of_eventuallyEq he
  have hv := hd.unique Complex.hasDerivAt_Gamma_one
  simp only [sub_self, Complex.cpow_zero, one_mul] at hv
  simp_rw [← Complex.ofReal_mul] at hv
  rw [← Complex.ofReal_neg, integral_complex_ofReal] at hv
  exact_mod_cast hv

private noncomputable def logGaussianMoment (u : ℝ) : ℝ :=
  2 * u * Real.log u * gaussianProfile 1 0 1 u

private theorem logGaussianMoment_integral :
    IntegrableOn logGaussianMoment (Ioi 0) ∧
      2 * (∫ u in Ioi (0 : ℝ), logGaussianMoment u) = -Real.eulerMascheroniConstant := by
  have he : (fun u : ℝ => (|(2 : ℝ)| * u ^ ((2 : ℝ) - 1)) •
      (Real.log (u ^ (2 : ℝ)) * Real.exp (-(u ^ (2 : ℝ))))) =
      fun u => 2 * logGaussianMoment u := by
    funext u
    norm_num [Real.rpow_two, Real.log_pow, logGaussianMoment, gaussianProfile]
    ring
  have hi := (integrableOn_Ioi_comp_rpow_iff
    (fun y : ℝ => Real.log y * Real.exp (-y)) (by norm_num : (2 : ℝ) ≠ 0)).mpr
      gamma_log_integral.1
  rw [he] at hi
  have hm : IntegrableOn logGaussianMoment (Ioi 0) := by
    have hh : IntegrableOn (fun u => (1 / 2 : ℝ) * (2 * logGaussianMoment u)) (Ioi 0) :=
      hi.const_mul _
    convert hh using 1
    ext u
    ring
  refine ⟨hm, ?_⟩
  have hv := integral_comp_rpow_Ioi (fun y : ℝ => Real.log y * Real.exp (-y))
    (by norm_num : (2 : ℝ) ≠ 0)
  rw [he, integral_const_mul, gamma_log_integral.2] at hv
  exact hv

private theorem pureTaylor_zero (γ u : ℝ) : pureTaylor 0 γ u = 1 := by
  unfold pureTaylor
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, profileTaylorCoefficient_zero, pow_zero, mul_one,
    Fin.sum_univ_zero, add_zero]

private theorem hasDerivAt_logGaussian_small {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun x => (gaussianProfile 1 0 1 x - 1) * Real.log x)
      (pureRemainder 0 1 u - logGaussianMoment u) u := by
  convert ((hasDerivAt_pureGaussian 1 u).sub_const 1).mul (Real.hasDerivAt_log hu) using 1
  simp only [pureRemainder, pureTaylor_zero, zero_add, pow_one, logGaussianMoment]
  ring

private theorem hasDerivAt_logGaussian_tail {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun x => gaussianProfile 1 0 1 x * Real.log x)
      (gaussianProfile 1 0 1 u / u - logGaussianMoment u) u := by
  convert (hasDerivAt_pureGaussian 1 u).mul (Real.hasDerivAt_log hu) using 1
  simp only [logGaussianMoment]
  ring

private theorem tendsto_logGaussian_small_zero :
    Tendsto (fun u => (gaussianProfile 1 0 1 u - 1) * Real.log u) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_purePrimitive_zero 1 1).mul
    (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one)
  simp only [Real.rpow_one, mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu₀ : u ≠ 0 := ne_of_gt hu
  simp only [purePrimitive, pureTaylor_one, pow_one]
  field_simp

private theorem tendsto_logGaussian_tail_zero :
    Tendsto (fun u => gaussianProfile 1 0 1 u * Real.log u) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun u : ℝ => u ^ 2 * Real.exp (-(u ^ 2)))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu₀ : 0 ≤ u := zero_le_one.trans hu
    have hl : 0 ≤ Real.log u := Real.log_nonneg hu
    have hq : Real.log u ≤ u ^ 2 := (Real.log_le_self hu₀).trans (by nlinarith)
    simp only [gaussianProfile, zero_mul, add_zero, one_mul, neg_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hl)]
    exact (mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
    have h1 : Tendsto (fun u : ℝ => (u ^ 2) ^ 1 * Real.exp (-(u ^ 2))) atTop (𝓝 0) := h0
    simpa only [pow_one] using h1

private theorem profileFinitePart_zero_eq_logGaussianMoment :
    profileFinitePart 0 1 0 1 zero_lt_one = ∫ u in Ioi (0 : ℝ), logGaussianMoment u := by
  have hL := logGaussianMoment_integral.1
  have hLs : IntegrableOn logGaussianMoment (Ioo 0 1) :=
    hL.mono_set (fun _ hu => hu.1)
  have hLt : IntegrableOn logGaussianMoment (Ioi 1) :=
    hL.mono_set (Ioi_subset_Ioi zero_le_one)
  have hR : IntegrableOn (pureRemainder 0 1) (Ioo 0 1) :=
    integrableOn_gaussianProfile_sub_taylor_div_pow_Ioo 0 1 0 1
  have hT : IntegrableOn (fun u => gaussianProfile 1 0 1 u / u) (Ioi 1) := by
    simpa only [zero_add, pow_one] using
      integrableOn_gaussianProfile_div_pow_Ioi_one 0 1 0 zero_lt_one
  have hs := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u (hu : u ∈ Ioo (0 : ℝ) 1) => hasDerivAt_logGaussian_small hu.1.ne')
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr (hR.sub hLs))
    tendsto_logGaussian_small_zero
    ((hasDerivAt_logGaussian_small one_ne_zero).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_sub hR hLs] at hs
  simp only [Real.log_one, mul_zero, sub_self] at hs
  have ht := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u (hu : u ∈ Ici (1 : ℝ)) =>
      hasDerivAt_logGaussian_tail (ne_of_gt (zero_lt_one.trans_le hu)))
    (hT.sub hLt) tendsto_logGaussian_tail_zero
  rw [integral_sub hT hLt] at ht
  simp only [Real.log_one, mul_zero, sub_self] at ht
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
    measurableSet_Ioi (hL.mono_set (fun _ hu => hu.1)) hLt
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one, integral_Ioc_eq_integral_Ioo] at hsplit
  unfold profileFinitePart
  change (∫ u in Ioo (0 : ℝ) 1, pureRemainder 0 1 u) +
    (∫ u in Ioi (1 : ℝ), gaussianProfile 1 0 1 u / u ^ (0 + 1)) - _ = _
  simp only [zero_add, pow_one, Fin.sum_univ_zero, sub_zero]
  linear_combination hs + ht - hsplit

/-- Euler's constant fixes the unit-rate degree-zero finite-part normalization. -/
theorem profileFinitePart_pure_zero_unit :
    2 * profileFinitePart 0 1 0 1 zero_lt_one = -Real.eulerMascheroniConstant := by
  rw [profileFinitePart_zero_eq_logGaussianMoment]
  exact logGaussianMoment_integral.2

/-- The pure-Gaussian even finite part with its harmonic/Euler normalization. -/
theorem profileFinitePart_pure_even (n : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    2 * profileFinitePart (2 * n) 1 0 γ hγ =
      ((-γ) ^ n / (n.factorial : ℝ)) *
        ((harmonic n : ℝ) - Real.eulerMascheroniConstant - Real.log γ) := by
  rw [profileFinitePart_pure_even_unit_base, profileFinitePart_pure_zero_unit]
  ring

/-- The manuscript even formula in every source dimension `d = 2*(n+1) ≥ 2`,
with `ψ(n+1) = harmonic n - Euler's constant` and the literal `2*M_d`. -/
theorem profileFinitePart_even (n : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    2 * profileFinitePart (2 * (n + 1)) u₀ u₂ γ hγ =
      u₀ * ((-γ) ^ (n + 1) / ((n + 1).factorial : ℝ)) *
        ((harmonic (n + 1) : ℝ) - Real.eulerMascheroniConstant - Real.log γ) +
      u₂ * ((-γ) ^ n / (n.factorial : ℝ)) *
        ((harmonic n : ℝ) - Real.eulerMascheroniConstant - Real.log γ) := by
  rw [profileFinitePart_even_unit_base, profileFinitePart_pure_zero_unit]
  ring

end EinsteinFull
