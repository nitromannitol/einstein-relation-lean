import EinsteinFull.Blueprint.G1.Proofs.S3RenewalScalar
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace EinsteinFull.Blueprint

/-! # Uniform estimates for the solution of a lattice renewal equation -/

@[nolint unusedArguments]
theorem sum_conv_exp_le (c1 b : ℝ) (hc1 : 0 < c1) (hb : 0 < b) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), Real.exp (-c1 * ((j - i : ℕ) : ℝ)) * Real.exp (-b * (i : ℝ)) ≤
      ((j : ℝ) + 1) * Real.exp (-(min c1 b) * (j : ℝ)) := by
  have hterm : ∀ i ∈ Finset.range (j + 1),
      Real.exp (-c1 * ((j - i : ℕ) : ℝ)) * Real.exp (-b * (i : ℝ)) ≤
        Real.exp (-(min c1 b) * (j : ℝ)) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by rw [Nat.cast_sub hij]
    rw [hcast]
    have h1 : min c1 b ≤ c1 := min_le_left _ _
    have h2 : min c1 b ≤ b := min_le_right _ _
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have hji : (0 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    nlinarith [mul_nonneg hji (sub_nonneg.mpr h1), mul_nonneg hi0 (sub_nonneg.mpr h2)]
  calc _ ≤ ∑ i ∈ Finset.range (j + 1), Real.exp (-(min c1 b) * (j : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ((j : ℝ) + 1) * Real.exp (-(min c1 b) * (j : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem lin_exp_le (c0 : ℝ) (hc0 : 0 < c0) (j : ℕ) :
    ((j : ℝ) + 1) * Real.exp (-c0 * (j : ℝ)) ≤ (1 + 2 / c0) * Real.exp (-(c0 / 2) * (j : ℝ)) := by
  set x : ℝ := c0 / 2 * (j : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hexp : Real.exp (-c0 * (j : ℝ)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    rw [hx]
    ring
  have hexp2 : Real.exp (-(c0 / 2) * (j : ℝ)) = Real.exp (-x) := by
    congr 1
    rw [hx]
    ring
  rw [hexp, hexp2]
  have hjx : (j : ℝ) = 2 * x / c0 := by
    rw [hx]
    field_simp
  have hxe : x * Real.exp (-x) ≤ 1 := by
    have h1 := Real.add_one_le_exp x
    have h2 : 0 < Real.exp (-x) := Real.exp_pos _
    have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have he1 : Real.exp (-x) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have he0 : 0 < Real.exp (-x) := Real.exp_pos _
  have : ((j : ℝ) + 1) * Real.exp (-x) = 2 / c0 * (x * Real.exp (-x)) + Real.exp (-x) := by
    rw [hjx]; field_simp
  calc ((j : ℝ) + 1) * (Real.exp (-x) * Real.exp (-x))
      = (((j : ℝ) + 1) * Real.exp (-x)) * Real.exp (-x) := by ring
    _ = (2 / c0 * (x * Real.exp (-x)) + Real.exp (-x)) * Real.exp (-x) := by rw [this]
    _ ≤ (2 / c0 * 1 + 1) * Real.exp (-x) := by
        apply mul_le_mul_of_nonneg_right _ he0.le
        have : 0 ≤ 2 / c0 := by positivity
        nlinarith
    _ = (1 + 2 / c0) * Real.exp (-x) := by ring

theorem renewal_estimates (U : ℕ → ℝ) (m : ℝ) (C1 c1 b : ℝ) (hC1 : 0 < C1) (hc1 : 0 < c1)
    (hb : 0 < b) (hU0 : U 0 = 1)
    (hU : ∀ n : ℕ, |U n - m⁻¹| ≤ C1 * Real.exp (-c1 * (n : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (h r : ℕ → ℝ) (R : ℝ), 0 ≤ R →
      (∀ j : ℕ, |r j| ≤ R * Real.exp (-b * (j : ℝ))) →
      (∀ j : ℕ, h j = ∑ i ∈ Finset.range (j + 1), U (j - i) * r i) →
      Summable r ∧ |m⁻¹ * ∑' j, r j| ≤ C * R ∧
      ∀ j : ℕ, |h j - m⁻¹ * ∑' i, r i| ≤ C * R * Real.exp (-(min c1 b / 2) * (j : ℝ)) := by
  have hρ : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hρ0 : 0 < Real.exp (-b) := Real.exp_pos _
  have h1ρ : 0 < 1 - Real.exp (-b) := sub_pos.mpr hρ
  have hc0 : 0 < min c1 b := lt_min hc1 hb
  have hm : |m⁻¹| ≤ 1 + C1 := by
    have h0 := hU 0
    rw [hU0] at h0
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at h0
    calc |m⁻¹| = |1 - (1 - m⁻¹)| := by ring_nf
      _ ≤ |(1 : ℝ)| + |1 - m⁻¹| := abs_sub _ _
      _ ≤ 1 + C1 := by rw [abs_one]; linarith
  refine ⟨min c1 b / 2, C1 * (1 + 2 / min c1 b) + (1 + C1) / (1 - Real.exp (-b)),
    half_pos hc0, by positivity, ?_⟩
  intro h r R hR hr hh
  have hgeom : ∀ j : ℕ, Real.exp (-b * (j : ℝ)) = Real.exp (-b) ^ j := by
    intro j
    rw [mul_comm, Real.exp_nat_mul]
  have hsum : Summable (fun j : ℕ => R * Real.exp (-b) ^ j) :=
    (summable_geometric_of_lt_one hρ0.le hρ).mul_left R
  have hrs : Summable r := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => ?_) hsum)
    rw [Real.norm_eq_abs, ← hgeom]
    exact hr j
  have hCpos : 0 < C1 * (1 + 2 / min c1 b) + (1 + C1) / (1 - Real.exp (-b)) := by positivity
  have hgeo := hasSum_geometric_of_lt_one hρ0.le hρ
  have htot : |∑' j, r j| ≤ R * (1 - Real.exp (-b))⁻¹ := by
    have := tsum_of_norm_bounded (hgeo.mul_left R) (f := r) (fun j => by
      rw [Real.norm_eq_abs, ← hgeom]; exact hr j)
    simpa only [Real.norm_eq_abs] using this
  have hMR : |m⁻¹ * ∑' j, r j| ≤ (1 + C1) / (1 - Real.exp (-b)) * R := by
    rw [abs_mul]
    calc |m⁻¹| * |∑' j, r j| ≤ (1 + C1) * (R * (1 - Real.exp (-b))⁻¹) :=
          mul_le_mul hm htot (abs_nonneg _) (by linarith [abs_nonneg m⁻¹])
      _ = (1 + C1) / (1 - Real.exp (-b)) * R := by field_simp
  refine ⟨hrs, ?_, ?_⟩
  · calc |m⁻¹ * ∑' j, r j| ≤ (1 + C1) / (1 - Real.exp (-b)) * R := hMR
      _ ≤ (C1 * (1 + 2 / min c1 b) + (1 + C1) / (1 - Real.exp (-b))) * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        have : 0 ≤ C1 * (1 + 2 / min c1 b) := by positivity
        linarith
  · intro j
    have hdecomp : ∑' i, r i = ∑ i ∈ Finset.range (j + 1), r i + ∑' i, r (i + (j + 1)) :=
      (Summable.sum_add_tsum_nat_add (j + 1) hrs).symm
    set T : ℝ := ∑' i, r (i + (j + 1)) with hT
    have hTb : |T| ≤ R * Real.exp (-b) ^ (j + 1) * (1 - Real.exp (-b))⁻¹ := by
      have := tsum_of_norm_bounded (hgeo.mul_left (R * Real.exp (-b) ^ (j + 1)))
        (f := fun i => r (i + (j + 1))) (fun i => by
          rw [Real.norm_eq_abs]
          calc |r (i + (j + 1))| ≤ R * Real.exp (-b * ((i + (j + 1) : ℕ) : ℝ)) := hr _
            _ = R * Real.exp (-b) ^ (i + (j + 1)) := by rw [hgeom]
            _ = R * Real.exp (-b) ^ (j + 1) * Real.exp (-b) ^ i := by rw [pow_add]; ring)
      simpa only [Real.norm_eq_abs] using this
    have hcalc : h j - m⁻¹ * ∑' i, r i =
        ∑ i ∈ Finset.range (j + 1), (U (j - i) - m⁻¹) * r i - m⁻¹ * T := by
      have hsplit : ∑ i ∈ Finset.range (j + 1), (U (j - i) - m⁻¹) * r i =
          ∑ i ∈ Finset.range (j + 1), U (j - i) * r i -
            m⁻¹ * ∑ i ∈ Finset.range (j + 1), r i := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hh j, hdecomp, hsplit]
      ring
    rw [hcalc]
    have hA : |∑ i ∈ Finset.range (j + 1), (U (j - i) - m⁻¹) * r i| ≤
        C1 * R * ((1 + 2 / min c1 b) * Real.exp (-(min c1 b / 2) * (j : ℝ))) := by
      calc |∑ i ∈ Finset.range (j + 1), (U (j - i) - m⁻¹) * r i|
          ≤ ∑ i ∈ Finset.range (j + 1), |(U (j - i) - m⁻¹) * r i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (j + 1), C1 * R *
            (Real.exp (-c1 * ((j - i : ℕ) : ℝ)) * Real.exp (-b * (i : ℝ))) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [abs_mul]
            calc |U (j - i) - m⁻¹| * |r i|
                ≤ (C1 * Real.exp (-c1 * ((j - i : ℕ) : ℝ))) * (R * Real.exp (-b * (i : ℝ))) :=
                  mul_le_mul (hU _) (hr i) (abs_nonneg _) (by positivity)
              _ = _ := by ring
        _ = C1 * R * ∑ i ∈ Finset.range (j + 1),
            (Real.exp (-c1 * ((j - i : ℕ) : ℝ)) * Real.exp (-b * (i : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ C1 * R * (((j : ℝ) + 1) * Real.exp (-(min c1 b) * (j : ℝ))) := by
            apply mul_le_mul_of_nonneg_left (sum_conv_exp_le c1 b hc1 hb j) (by positivity)
        _ ≤ C1 * R * ((1 + 2 / min c1 b) * Real.exp (-(min c1 b / 2) * (j : ℝ))) := by
            apply mul_le_mul_of_nonneg_left (lin_exp_le (min c1 b) hc0 j) (by positivity)
    have hB : |m⁻¹ * T| ≤ (1 + C1) / (1 - Real.exp (-b)) * R *
        Real.exp (-(min c1 b / 2) * (j : ℝ)) := by
      rw [abs_mul]
      have hpow : Real.exp (-b) ^ (j + 1) ≤ Real.exp (-(min c1 b / 2) * (j : ℝ)) := by
        calc Real.exp (-b) ^ (j + 1) ≤ Real.exp (-b) ^ j :=
              pow_le_pow_of_le_one hρ0.le hρ.le (Nat.le_succ j)
          _ = Real.exp (-b * (j : ℝ)) := (hgeom j).symm
          _ ≤ Real.exp (-(min c1 b / 2) * (j : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have : min c1 b / 2 ≤ b := by
                have := min_le_right c1 b
                linarith
              have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
              nlinarith
      calc |m⁻¹| * |T| ≤ (1 + C1) * (R * Real.exp (-b) ^ (j + 1) * (1 - Real.exp (-b))⁻¹) :=
            mul_le_mul hm hTb (abs_nonneg _) (by linarith [abs_nonneg m⁻¹])
        _ = (1 + C1) / (1 - Real.exp (-b)) * R * Real.exp (-b) ^ (j + 1) := by
            field_simp
        _ ≤ (1 + C1) / (1 - Real.exp (-b)) * R * Real.exp (-(min c1 b / 2) * (j : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
    calc |∑ i ∈ Finset.range (j + 1), (U (j - i) - m⁻¹) * r i - m⁻¹ * T|
        ≤ |∑ i ∈ Finset.range (j + 1), (U (j - i) - m⁻¹) * r i| + |m⁻¹ * T| := abs_sub _ _
      _ ≤ _ := by
        have := add_le_add hA hB
        calc _ ≤ _ := this
          _ = _ := by ring

end EinsteinFull.Blueprint
