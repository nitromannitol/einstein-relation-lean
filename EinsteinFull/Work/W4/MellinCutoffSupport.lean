import EinsteinFull.Work.W4.ProfileFinitePartSupport
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact cutoff integration for the literal Gaussian profile finite part. -/

open MeasureTheory Set
open scoped BigOperators

namespace EinsteinFull

/-- The noncritical inverse-power integral away from zero. -/
theorem integral_inv_pow_Ioo {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    {k : ℕ} (hk : 0 < k) :
    (∫ u in Ioo s 1, (1 : ℝ) / u ^ (k + 1)) = (1 / s ^ k - 1) / (k : ℝ) := by
  have he : (-((k + 1 : ℕ) : ℤ)) + 1 = -(k : ℤ) := by omega
  have h := integral_zpow (a := s) (b := (1 : ℝ)) (n := -((k + 1 : ℕ) : ℤ))
    (Or.inr ⟨by omega, notMem_uIcc_of_lt hs zero_lt_one⟩)
  rw [intervalIntegral.integral_of_le hs₁, integral_Ioc_eq_integral_Ioo, he] at h
  simp only [zpow_neg, zpow_natCast, one_pow, inv_one, Int.cast_neg,
    Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one] at h
  have hd : -((k : ℝ) + 1) + 1 = -(k : ℝ) := by ring
  rw [hd, div_neg, ← neg_div, neg_sub] at h
  simpa only [← Int.natCast_succ, zpow_natCast, one_div] using h

/-- Each subcritical Taylor monomial has its exact bounded-interval integral. -/
theorem integral_monomial_div_pow_Ioo {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    {d j : ℕ} (hj : j < d) (c : ℝ) :
    (∫ u in Ioo s 1, c * u ^ j / u ^ (d + 1)) =
      c / ((d - j : ℕ) : ℝ) * (1 / s ^ (d - j) - 1) := by
  have hfun : (fun u : ℝ => c * u ^ j / u ^ (d + 1)) =ᵐ[volume.restrict (Ioo s 1)]
      (fun u : ℝ => c * (1 / u ^ (d - j + 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu₀ : u ≠ 0 := ne_of_gt (hs.trans hu.1)
    have he : d + 1 = j + (d - j + 1) := by omega
    rw [he, pow_add]
    field_simp
  rw [integral_congr_ae hfun, integral_const_mul,
    integral_inv_pow_Ioo hs hs₁ (by omega : 0 < d - j)]
  ring

/-- The critical Taylor monomial gives the logarithm with the manuscript's sign. -/
theorem integral_critical_monomial_div_pow_Ioo {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (d : ℕ) (c : ℝ) :
    (∫ u in Ioo s 1, c * u ^ d / u ^ (d + 1)) = c * Real.log (1 / s) := by
  have hfun : (fun u : ℝ => c * u ^ d / u ^ (d + 1)) =ᵐ[volume.restrict (Ioo s 1)]
      (fun u : ℝ => c * (1 / u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu₀ : u ≠ 0 := ne_of_gt (hs.trans hu.1)
    rw [pow_succ]
    field_simp
  rw [integral_congr_ae hfun, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs₁,
    integral_one_div_of_pos hs zero_lt_one]

private theorem integrableOn_div_pow_Icc {s : ℝ} (hs : 0 < s) (n : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn (fun u => f u / u ^ n) (Icc s 1) := by
  apply ContinuousOn.integrableOn_Icc
  exact hf.continuousOn.div (continuous_id.pow n).continuousOn
    (fun u hu => pow_ne_zero _ (ne_of_gt (hs.trans_le hu.1)))

/-- Every coefficient monomial is integrable on a cutoff interval. -/
theorem integrableOn_monomial_div_pow_Ioo {s : ℝ} (hs : 0 < s)
    (d j : ℕ) (c : ℝ) :
    IntegrableOn (fun u : ℝ => c * u ^ j / u ^ (d + 1)) (Ioo s 1) := by
  exact (integrableOn_div_pow_Icc hs (d + 1)
    (continuous_const.mul (continuous_id.pow j))).mono_set Ioo_subset_Icc_self

/-- Integrating the actual Taylor polynomial keeps its critical logarithmic term. -/
theorem integral_profileTaylor_div_pow_Ioo {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (d : ℕ) (u₀ u₂ γ : ℝ) :
    (∫ u in Ioo s 1,
      (∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
        u ^ (d + 1)) =
      (∑ j : Fin d, profileTaylorCoefficient u₀ u₂ γ j.val /
        ((d - j.val : ℕ) : ℝ) * (1 / s ^ (d - j.val) - 1)) +
      profileTaylorCoefficient u₀ u₂ γ d * Real.log (1 / s) := by
  simp_rw [Finset.sum_div]
  rw [integral_finset_sum (μ := volume.restrict (Ioo s 1))
    (f := fun (j : Fin (d + 1)) (u : ℝ) =>
      profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val / u ^ (d + 1))
    _ (fun j _ => integrableOn_monomial_div_pow_Ioo hs d j.val _), Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact integral_monomial_div_pow_Ioo hs hs₁ j.isLt _
  · exact integral_critical_monomial_div_pow_Ioo hs hs₁ d _

/-- On the cutoff interval the actual profile splits into its Taylor sum and remainder. -/
theorem integral_gaussianProfile_sub_taylor_cutoff {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (d : ℕ) (u₀ u₂ γ : ℝ) :
    (∫ u in Ioo s 1, gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) =
      (∫ u in Ioo s 1,
        (gaussianProfile u₀ u₂ γ u -
          ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
            u ^ (d + 1)) +
      (∑ j : Fin d, profileTaylorCoefficient u₀ u₂ γ j.val /
        ((d - j.val : ℕ) : ℝ) * (1 / s ^ (d - j.val) - 1)) +
      profileTaylorCoefficient u₀ u₂ γ d * Real.log (1 / s) := by
  have hH := (integrableOn_div_pow_Icc hs (d + 1)
    (contDiff_gaussianProfile u₀ u₂ γ 0).continuous).mono_set Ioo_subset_Icc_self
  have hP : IntegrableOn (fun u : ℝ =>
      (∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
        u ^ (d + 1)) (Ioo s 1) := by
    simp_rw [Finset.sum_div]
    exact integrable_finset_sum _ (fun j _ => integrableOn_monomial_div_pow_Ioo hs d j.val _)
  simp_rw [sub_div]
  rw [integral_sub hH hP, integral_profileTaylor_div_pow_Ioo hs hs₁]
  ring

private theorem integral_Ioo_split_at {s : ℝ} (hs : 0 ≤ s) (hs₁ : s ≤ 1)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo 0 1)) :
    (∫ u in Ioo (0 : ℝ) 1, f u) =
      (∫ u in Ioo (0 : ℝ) s, f u) + (∫ u in Ioo s 1, f u) := by
  have hf' : IntegrableOn f (Ioc 0 1) := (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hf
  have h := setIntegral_union (Ioc_disjoint_Ioc_of_le (a := (0 : ℝ))
    (b := s) (c := s) (d := 1) le_rfl) measurableSet_Ioc
    (hf'.mono_set (Ioc_subset_Ioc_right hs₁)) (hf'.mono_set (Ioc_subset_Ioc_left hs))
  simpa only [Ioc_union_Ioc_eq_Ioc hs hs₁, integral_Ioc_eq_integral_Ioo] using h

/-- The profile integral over a positive half-line splits at the finite-part base point. -/
theorem integral_gaussianProfile_div_pow_Ioi_split {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (d : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (∫ u in Ioi s, gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) =
      (∫ u in Ioo s 1, gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) +
      (∫ u in Ioi (1 : ℝ), gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) := by
  have hlocal := (integrableOn_div_pow_Icc hs (d + 1)
    (contDiff_gaussianProfile u₀ u₂ γ 0).continuous).mono_set Ioc_subset_Icc_self
  have h := setIntegral_union (Ioc_disjoint_Ioi_same (a := s) (b := (1 : ℝ)))
    measurableSet_Ioi hlocal (integrableOn_gaussianProfile_div_pow_Ioi_one d u₀ u₂ hγ)
  simpa only [Ioc_union_Ioi_eq_Ioi hs₁, integral_Ioc_eq_integral_Ioo] using h

/-- Exact unscaled cutoff identity for the frozen finite-part convention. -/
theorem gaussianProfile_mellin_cutoff_unscaled {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (d : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (∫ u in Ioi s, gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) =
      (∑ j : Fin d, profileTaylorCoefficient u₀ u₂ γ j.val /
        ((d - j.val : ℕ) : ℝ) * (1 / s ^ (d - j.val))) +
      profileTaylorCoefficient u₀ u₂ γ d * Real.log (1 / s) +
      profileFinitePart d u₀ u₂ γ hγ -
      (∫ u in Ioo (0 : ℝ) s,
        (gaussianProfile u₀ u₂ γ u -
          ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
            u ^ (d + 1)) := by
  rw [integral_gaussianProfile_div_pow_Ioi_split hs hs₁ d u₀ u₂ hγ,
    integral_gaussianProfile_sub_taylor_cutoff hs hs₁ d u₀ u₂ γ, profileFinitePart,
    integral_Ioo_split_at hs.le hs₁
      (integrableOn_gaussianProfile_sub_taylor_div_pow_Ioo d u₀ u₂ γ)]
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  ring

/-- The exact Mellin cutoff formula behind `e:mellin`, before estimating the last integral.
The formula holds at every natural order, in particular at the manuscript's `d ≥ 2`. -/
theorem gaussianProfile_mellin_cutoff {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (d : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    2 * s ^ d * (∫ u in Ioi s, gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) =
      (∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
        ((d - j.val : ℕ) : ℝ)) * s ^ j.val) +
      2 * profileTaylorCoefficient u₀ u₂ γ d * s ^ d * Real.log (1 / s) +
      2 * profileFinitePart d u₀ u₂ γ hγ * s ^ d -
      2 * s ^ d * (∫ u in Ioo (0 : ℝ) s,
        (gaussianProfile u₀ u₂ γ u -
          ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
            u ^ (d + 1)) := by
  have hmono (j : Fin d) :
      2 * s ^ d * (profileTaylorCoefficient u₀ u₂ γ j.val /
        ((d - j.val : ℕ) : ℝ) * (1 / s ^ (d - j.val))) =
      (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
        ((d - j.val : ℕ) : ℝ)) * s ^ j.val := by
    have hp : s ^ d = s ^ j.val * s ^ (d - j.val) := by
      rw [← pow_add, Nat.add_sub_of_le j.isLt.le]
    rw [hp]
    field_simp
  rw [gaussianProfile_mellin_cutoff_unscaled hs hs₁ d u₀ u₂ hγ,
    mul_sub, mul_add, mul_add, Finset.mul_sum]
  simp_rw [hmono]
  ring

end EinsteinFull
