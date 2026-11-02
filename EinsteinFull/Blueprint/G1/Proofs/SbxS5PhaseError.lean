import EinsteinFull.Blueprint.G1.Proofs.S3RenewalEstimates
import EinsteinFull.Regeneration.LatticeSupport
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinFull.Blueprint.G1.node_rt_u3A_remainder_u2D_moment
import EinsteinFull.Blueprint.G1.node_rt_u3A_m_u2D_renewal
import EinsteinFull.Blueprint.Roots.node_rt_u3A_renewal
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Regeneration.Measurability

open MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-! Scalar support for `rt:local-mixing#phase-error` (paper/main.tex:508–518).

These lemmas solve the scalar renewal equation, including its infinite tail,
and supply bounded-observable renewal identities and cycle-window tails.
The analytic remainder bound and the four-dependency reduction remain open.
-/

/-- Subtracting the renewal limit retains the entire omitted infinite tail. -/
theorem renewal_phase_error_identity (p h r : ℕ → ℝ) (mean : ℝ)
    (hp : p 0 = 0) (hr : Summable r)
    (hh : ∀ j, h j = r j + ∑ n ∈ Finset.range (j + 1), p n * h (j - n))
    (j : ℕ) :
    h j - mean⁻¹ * ∑' n, r n =
      (∑ n ∈ Finset.range (j + 1),
        ((∑' a, latticeConvolutionPower p a (j - n)) - mean⁻¹) * r n) -
      mean⁻¹ * ∑' n, r (j + 1 + n) := by
  have hconv := renewal_conv p h r
    (fun n => ∑' a, latticeConvolutionPower p a n) (U_recursion p hp) hh j
  have hsplit : (∑' n, r n) =
      (∑ n ∈ Finset.range (j + 1), r n) + ∑' n, r (j + 1 + n) := by
    simpa only [Nat.add_comm] using (hr.sum_add_tsum_nat_add (j + 1)).symm
  rw [hconv, hsplit]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Scalar renewal constants depend only on the common exponential envelope,
so they are chosen before the renewal sequence and its limiting mean. -/
theorem renewal_estimates_uniform (C1 c1 b : ℝ) (hC1 : 0 < C1)
    (hc1 : 0 < c1) (hb : 0 < b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (U : ℕ → ℝ) (mean : ℝ),
      U 0 = 1 →
      (∀ n : ℕ, |U n - mean⁻¹| ≤ C1 * Real.exp (-c1 * (n : ℝ))) →
      ∀ (h r : ℕ → ℝ) (R : ℝ), 0 ≤ R →
      (∀ j : ℕ, |r j| ≤ R * Real.exp (-b * (j : ℝ))) →
      (∀ j : ℕ, h j = ∑ i ∈ Finset.range (j + 1), U (j - i) * r i) →
      Summable r ∧ |mean⁻¹ * ∑' j, r j| ≤ C * R ∧
      ∀ j : ℕ, |h j - mean⁻¹ * ∑' i, r i| ≤ C * R * Real.exp (-c * (j : ℝ)) := by
  have hρ : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hρ0 : 0 < Real.exp (-b) := Real.exp_pos _
  have h1ρ : 0 < 1 - Real.exp (-b) := sub_pos.mpr hρ
  have hc0 : 0 < min c1 b := lt_min hc1 hb
  refine ⟨min c1 b / 2, C1 * (1 + 2 / min c1 b) + (1 + C1) / (1 - Real.exp (-b)),
    half_pos hc0, by positivity, ?_⟩
  intro U m hU0 hU
  have hm : |m⁻¹| ≤ 1 + C1 := by
    have h0 := hU 0
    rw [hU0] at h0
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at h0
    calc |m⁻¹| = |1 - (1 - m⁻¹)| := by ring_nf
      _ ≤ |(1 : ℝ)| + |1 - m⁻¹| := abs_sub _ _
      _ ≤ 1 + C1 := by rw [abs_one]; linarith
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

/-- Phase-error constants chosen before the renewal law, its mean, cycle count,
and observable size. This order permits uniform estimates over environments. -/
theorem renewal_phase_error_estimates_uniform (C₁ c₁ b C₀ : ℝ)
    (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hb : 0 < b)
    (hC₀ : 0 < C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (p : ℕ → ℝ) (mean : ℝ), p 0 = 0 →
      (∀ n : ℕ, |(∑' a, latticeConvolutionPower p a n) - mean⁻¹| ≤
        C₁ * Real.exp (-c₁ * n)) →
      ∀ (m : ℕ) (N : ℝ), 0 ≤ N → ∀ h r : ℕ → ℝ,
      (∀ j, |r j| ≤ C₀ * Real.exp (C₀ * m - b * j) * N) →
      (∀ j, h j = r j + ∑ n ∈ Finset.range (j + 1), p n * h (j - n)) →
      Summable r ∧ |mean⁻¹ * ∑' n, r n| ≤ C * Real.exp (C * m) * N ∧
      ∀ j : ℕ,
        h j - mean⁻¹ * ∑' n, r n =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a, latticeConvolutionPower p a (j - n)) - mean⁻¹) * r n) -
          mean⁻¹ * ∑' n, r (j + 1 + n) ∧
        |h j - mean⁻¹ * ∑' n, r n| ≤ C * Real.exp (C * m - c * j) * N := by
  obtain ⟨c, D, hc, hD, hest⟩ := renewal_estimates_uniform C₁ c₁ b hC₁ hc₁ hb
  let C := max C₀ (D * C₀)
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hDC : D * C₀ ≤ C := le_max_right _ _
  have hC : 0 < C := lt_of_lt_of_le hC₀ hC₀C
  refine ⟨c, C, hc, hC, ?_⟩
  intro p mean hp hU m N hN h r hr hh
  have hU₀ : (∑' a, latticeConvolutionPower p a 0) = 1 := by
    rw [tsum_lcp_eq_sum p hp 0 1 (by omega)]
    simp only [Finset.sum_range_one, latticeConvolutionPower, ↓reduceIte]
  let R := C₀ * Real.exp (C₀ * m) * N
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg hC₀.le (Real.exp_pos _).le) hN
  have hr' : ∀ j : ℕ, |r j| ≤ R * Real.exp (-b * j) := by
    intro j
    calc |r j| ≤ C₀ * Real.exp (C₀ * m - b * j) * N := hr j
      _ = R * Real.exp (-b * j) := by
        dsimp only [R]
        rw [sub_eq_add_neg, Real.exp_add, ← neg_mul]
        ring
  obtain ⟨hrs, hlim, herr⟩ := hest (fun n => ∑' a, latticeConvolutionPower p a n) mean hU₀ hU h r R hR hr'
    (renewal_conv p h r (fun n => ∑' a, latticeConvolutionPower p a n)
      (U_recursion p hp) hh)
  have hpref : D * R ≤ C * Real.exp (C * m) * N := by
    calc D * R = (D * C₀) * Real.exp (C₀ * m) * N := by dsimp only [R]; ring
      _ ≤ C * Real.exp (C * m) * N := by
        apply mul_le_mul_of_nonneg_right _ hN
        exact mul_le_mul hDC (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hC₀C (Nat.cast_nonneg m)))
          (Real.exp_pos _).le hC.le
  refine ⟨hrs, hlim.trans hpref, fun j => ⟨renewal_phase_error_identity p h r mean hp hrs hh j, ?_⟩⟩
  calc |h j - mean⁻¹ * ∑' n, r n|
      ≤ D * R * Real.exp (-c * j) := herr j
    _ ≤ (C * Real.exp (C * m) * N) * Real.exp (-c * j) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = C * Real.exp (C * m - c * j) * N := by
      rw [sub_eq_add_neg, Real.exp_add, ← neg_mul]
      ring

/-- The scalar phase-error estimates, with constants chosen before the cycle
count and observable size. The sole cycle dependence is `exp(C*m)`. -/
theorem renewal_phase_error_estimates (p : ℕ → ℝ) (mean C₁ c₁ b C₀ : ℝ)
    (hp : p 0 = 0) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hb : 0 < b)
    (hC₀ : 0 < C₀)
    (hU : ∀ n : ℕ, |(∑' a, latticeConvolutionPower p a n) - mean⁻¹| ≤
      C₁ * Real.exp (-c₁ * n)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (m : ℕ) (N : ℝ), 0 ≤ N → ∀ h r : ℕ → ℝ,
      (∀ j, |r j| ≤ C₀ * Real.exp (C₀ * m - b * j) * N) →
      (∀ j, h j = r j + ∑ n ∈ Finset.range (j + 1), p n * h (j - n)) →
      Summable r ∧ |mean⁻¹ * ∑' n, r n| ≤ C * Real.exp (C * m) * N ∧
      ∀ j : ℕ,
        h j - mean⁻¹ * ∑' n, r n =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a, latticeConvolutionPower p a (j - n)) - mean⁻¹) * r n) -
          mean⁻¹ * ∑' n, r (j + 1 + n) ∧
        |h j - mean⁻¹ * ∑' n, r n| ≤ C * Real.exp (C * m - c * j) * N := by
  obtain ⟨c, C, hc, hC, hest⟩ :=
    renewal_phase_error_estimates_uniform C₁ c₁ b C₀ hC₁ hc₁ hb hC₀
  exact ⟨c, C, hc, hC, hest p mean hp hU⟩

/-- Sampling the continuous-time bound on a lattice with `lam² * Δ = 1`
gives a geometric bound independent of the force and of the phase. -/
theorem phase_remainder_bound (r : ℝ≥0 → ℝ) (C b lam N : ℝ) (m : ℕ)
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (Δ : ℝ≥0) (hΔ : lam ^ 2 * (Δ : ℝ) = 1)
    (hr : ∀ t : ℝ≥0, |r t| ≤ C * Real.exp (C * m - b * lam ^ 2 * (t : ℝ)) * N)
    (s : ℝ≥0) (j : ℕ) :
    |r (s + j * Δ)| ≤ C * Real.exp (C * m - b * j) * N := by
  have htime : b * lam ^ 2 * ((s : ℝ) + (j : ℝ) * (Δ : ℝ)) =
      b * lam ^ 2 * (s : ℝ) + b * j := by
    calc _ = b * lam ^ 2 * (s : ℝ) + b * j * (lam ^ 2 * (Δ : ℝ)) := by ring
      _ = _ := by rw [hΔ, mul_one]
  have hbs : 0 ≤ b * lam ^ 2 * (s : ℝ) :=
    mul_nonneg (mul_nonneg hb (sq_nonneg lam)) s.coe_nonneg
  calc |r (s + j * Δ)|
      ≤ C * Real.exp (C * m - b * lam ^ 2 * ((s + j * Δ : ℝ≥0) : ℝ)) * N := hr _
    _ ≤ C * Real.exp (C * m - b * j) * N := by
      apply mul_le_mul_of_nonneg_right _ hN
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, htime]
      linarith only [hbs]

/-- The scalar phase-error argument in the continuous-time notation used by
the terminal observable. Its constants precede the force, cycle count, size,
and phase; the analytic remainder bound and recurrence are separate inputs. -/
theorem renewal_phase_error_on_lattice (p : ℕ → ℝ) (mean C₁ c₁ b C₀ : ℝ)
    (hp : p 0 = 0) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hb : 0 < b)
    (hC₀ : 0 < C₀)
    (hU : ∀ n : ℕ, |(∑' a, latticeConvolutionPower p a n) - mean⁻¹| ≤
      C₁ * Real.exp (-c₁ * n)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (lam : ℝ) (Δ : ℝ≥0), lam ^ 2 * (Δ : ℝ) = 1 →
      ∀ (m : ℕ) (N : ℝ), 0 ≤ N → ∀ h r : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0, |r t| ≤ C₀ * Real.exp (C₀ * m - b * lam ^ 2 * (t : ℝ)) * N) →
      ∀ s : ℝ≥0,
      (∀ j : ℕ, h (s + j * Δ) = r (s + j * Δ) +
        ∑ n ∈ Finset.range (j + 1), p n * h (s + (j - n : ℕ) * Δ)) →
      let H := mean⁻¹ * ∑' n : ℕ, r (s + n * Δ)
      Summable (fun n : ℕ => r (s + n * Δ)) ∧
      |H| ≤ C * Real.exp (C * m) * N ∧ ∀ j : ℕ,
        h (s + j * Δ) - H =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a, latticeConvolutionPower p a (j - n)) - mean⁻¹) * r (s + n * Δ)) -
          mean⁻¹ * ∑' n : ℕ, r (s + (j + 1 + n : ℕ) * Δ) ∧
        |h (s + j * Δ) - H| ≤ C * Real.exp (C * m - c * j) * N := by
  obtain ⟨c, C, hc, hC, hest⟩ :=
    renewal_phase_error_estimates p mean C₁ c₁ b C₀ hp hC₁ hc₁ hb hC₀ hU
  refine ⟨c, C, hc, hC, ?_⟩
  intro lam Δ hΔ m N hN h r hr s hh
  exact hest m N hN (fun j => h (s + j * Δ)) (fun j => r (s + j * Δ))
    (phase_remainder_bound r C₀ b lam N m hC₀.le hb.le hN Δ hΔ hr s) hh

/-- The canonical-cycle renewal statement applies to every cycle count whose
recorded half-space contains the observation support. Enlarging the radius
to `(10*m+1)*l` makes its canonical cycle count exactly `m`. -/
theorem m_renewal_eq_of_support (hren : node_rt_u3A_m_u2D_renewalStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (A : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hsupport : 10 * (m : ℝ) * l - l - A ≥ -2 * l)
    (G : FieldPair d → ℝ)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G)
    (hbG : Regeneration.BoundedRealTest G) :
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let h := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    ∀ t : ℝ≥0, h t = r t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * h (t - n * Δ) := by
  let A' := (10 * (m : ℝ) + 1) * l
  have hm₀ : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA' : l ≤ A' := by dsimp only [A']; nlinarith only [mul_nonneg hm₀ hl.le]
  have hAA' : A ≤ A' := by dsimp only [A']; linarith only [hsupport]
  have hquot : (A' / l - 1) / 10 = (m : ℝ) := by
    dsimp only [A']
    rw [mul_div_cancel_right₀ _ hl.ne']
    ring
  have hcanonical : max 1 ⌈(A' / l - 1) / 10⌉₊ = m := by
    rw [hquot, Nat.ceil_natCast, max_eq_right hm]
  have hG' : Measurable[localSigma {x : Vec d | euclideanNorm x < A' / lam}] G :=
    hG.mono (Probability.localSigma_mono (fun x hx =>
      lt_of_lt_of_le hx (div_le_div_of_nonneg_right hAA' h₀.le))) le_rfl
  obtain ⟨_, _, hren'⟩ := hren d hd Λ₀ r₀ l δ hl hsep hδ₀ hδ₁
  have hresult := (hren' Q lam h₀ h₁ P K hK hD A' hA').2
  rw [hcanonical] at hresult
  dsimp only
  intro t
  exact (hresult G hG' hbG t).2.2

/-- Sampling the continuous-time renewal equation at one phase gives its
exact discrete recurrence, including the natural-number subtraction. -/
theorem renewal_eq_on_phase (p : ℕ → ℝ) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (h r : ℝ≥0 → ℝ)
    (hh : ∀ t : ℝ≥0, h t = r t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), p n * h (t - n * Δ))
    (s : ℝ≥0) (hs : s < Δ) (j : ℕ) :
    h (s + j * Δ) = r (s + j * Δ) +
      ∑ n ∈ Finset.range (j + 1), p n * h (s + (j - n : ℕ) * Δ) := by
  have hΔR : 0 < (Δ : ℝ) := hΔ
  have hsR : (s : ℝ) < (Δ : ℝ) := hs
  have hquot : ((s + j * Δ : ℝ≥0) : ℝ) / (Δ : ℝ) =
      (s : ℝ) / (Δ : ℝ) + (j : ℝ) := by
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, add_div,
      mul_div_cancel_right₀ _ hΔR.ne']
  have hzero : ⌊(s : ℝ) / (Δ : ℝ)⌋₊ = 0 :=
    Nat.floor_eq_zero.mpr ((div_lt_one hΔR).mpr hsR)
  have hfloor : ⌊((s + j * Δ : ℝ≥0) : ℝ) / (Δ : ℝ)⌋₊ = j := by
    rw [hquot, Nat.floor_add_natCast (by positivity), hzero, zero_add]
  rw [hh, hfloor]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnj : n ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  congr 2
  rw [add_tsub_assoc_of_le (mul_le_mul_of_nonneg_right
    (show (n : ℝ≥0) ≤ j by exact_mod_cast hnj) bot_le),
    ← tsub_mul, ← Nat.cast_tsub]

/-- Uniform scalar estimates for a continuous renewal equation. The phase
recurrence, infinite-tail identity and convergence share the same constants,
chosen before the law, mean, force, cycle count, observable and phase. -/
theorem renewal_phase_error_on_lattice_uniform (C₁ c₁ b C₀ : ℝ)
    (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hb : 0 < b) (hC₀ : 0 < C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (p : ℕ → ℝ) (mean : ℝ), p 0 = 0 →
      (∀ n : ℕ, |(∑' a, latticeConvolutionPower p a n) - mean⁻¹| ≤
        C₁ * Real.exp (-c₁ * n)) →
      ∀ (lam : ℝ) (Δ : ℝ≥0), lam ^ 2 * (Δ : ℝ) = 1 →
      ∀ (m : ℕ) (N : ℝ), 0 ≤ N → ∀ h r : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0, |r t| ≤ C₀ * Real.exp (C₀ * m - b * lam ^ 2 * (t : ℝ)) * N) →
      (∀ t : ℝ≥0, h t = r t +
        ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
          p n * h (t - n * Δ)) →
      ∀ s : ℝ≥0, s < Δ →
      let H := mean⁻¹ * ∑' n : ℕ, r (s + n * Δ)
      Summable (fun n : ℕ => r (s + n * Δ)) ∧
      |H| ≤ C * Real.exp (C * m) * N ∧ ∀ j : ℕ,
        h (s + j * Δ) = r (s + j * Δ) +
          ∑ n ∈ Finset.range (j + 1), p n * h (s + (j - n : ℕ) * Δ) ∧
        h (s + j * Δ) - H =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a, latticeConvolutionPower p a (j - n)) - mean⁻¹) * r (s + n * Δ)) -
          mean⁻¹ * ∑' n : ℕ, r (s + (j + 1 + n : ℕ) * Δ) ∧
        |h (s + j * Δ) - H| ≤ C * Real.exp (C * m - c * j) * N := by
  obtain ⟨c, C, hc, hC, hest⟩ :=
    renewal_phase_error_estimates_uniform C₁ c₁ b C₀ hC₁ hc₁ hb hC₀
  refine ⟨c, C, hc, hC, ?_⟩
  intro p mean hp hU lam Δ hΔ m N hN h r hr hh s hs
  have hΔpos : 0 < Δ := by
    by_contra! h
    have hz : Δ = 0 := le_antisymm h bot_le
    simp only [hz, NNReal.coe_zero, mul_zero, zero_ne_one] at hΔ
  have hphase := renewal_eq_on_phase p Δ hΔpos h r hh s hs
  obtain ⟨hrs, hlim, herr⟩ := hest p mean hp hU m N hN
    (fun j => h (s + j * Δ)) (fun j => r (s + j * Δ))
    (phase_remainder_bound r C₀ b lam N m hC₀.le hb.le hN Δ hΔ hr s) hphase
  exact ⟨hrs, hlim, fun j => ⟨hphase j, herr j⟩⟩

/-- An exponential moment of an extended time controls its tail, retaining
the infinite-time branch of the moment integrand. -/
theorem exponential_time_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (a B : ℝ) (ha : 0 ≤ a) (t : ℝ≥0)
    (hmoment : (∫⁻ ω, if T ω = ⊤ then ⊤ else
      ENNReal.ofReal (Real.exp (a * (T ω).toReal)) ∂μ) ≤ ENNReal.ofReal B) :
    μ {ω | (t : ℝ≥0∞) < T ω} ≤
      ENNReal.ofReal (B * Real.exp (-a * (t : ℝ))) := by
  have hs : MeasurableSet {ω | (t : ℝ≥0∞) < T ω} :=
    measurableSet_lt measurable_const hT
  have hbound : ENNReal.ofReal (Real.exp (a * (t : ℝ))) *
      μ {ω | (t : ℝ≥0∞) < T ω} ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ ω in {ω | (t : ℝ≥0∞) < T ω},
          ENNReal.ofReal (Real.exp (a * (t : ℝ))) ∂μ :=
        (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ ω in {ω | (t : ℝ≥0∞) < T ω},
          if T ω = ⊤ then ⊤ else
            ENNReal.ofReal (Real.exp (a * (T ω).toReal)) ∂μ := by
        apply setLIntegral_mono' hs
        intro ω hω
        split_ifs with htop
        · exact le_top
        · apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ ha
          simpa only [ENNReal.coe_toReal] using ENNReal.toReal_mono htop hω.le
      _ ≤ ∫⁻ ω, if T ω = ⊤ then ⊤ else
          ENNReal.ofReal (Real.exp (a * (T ω).toReal)) ∂μ :=
        setLIntegral_le_lintegral _ _
      _ ≤ _ := hmoment
  have hdiv : μ {ω | (t : ℝ≥0∞) < T ω} ≤
      ENNReal.ofReal B / ENNReal.ofReal (Real.exp (a * (t : ℝ))) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))
      (Or.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using hbound
  calc
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (Real.exp (a * (t : ℝ))) := hdiv
    _ = ENNReal.ofReal (B / Real.exp (a * (t : ℝ))) :=
      (ENNReal.ofReal_div_of_pos (Real.exp_pos _)).symm
    _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]

/-- The cycle-window tail bound follows directly from the corresponding
regeneration exponential moment, for either of the measures in `rt:renewal`. -/
theorem regeneration_cycle_tail_of_moment (d : ℕ) (hd : 2 ≤ d)
    (lam l a B : ℝ) (ha : 0 ≤ a) (m : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hmoment : (∫⁻ ωz, if regenerationTime hd lam l (m + 1) ωz.2 = ⊤ then ⊤ else
      ENNReal.ofReal (Real.exp (a * lam ^ 2 *
        (regenerationTime hd lam l (m + 1) ωz.2).toReal)) ∂μ) ≤
      ENNReal.ofReal B) (t : ℝ≥0) :
    μ {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} ≤
      ENNReal.ofReal (B * Real.exp (-a * lam ^ 2 * (t : ℝ))) := by
  calc
    _ ≤ μ {ωz | (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} :=
      measure_mono (fun _ hωz => hωz.2)
    _ ≤ _ := by
      simpa only [neg_mul] using exponential_time_tail μ
        (fun ωz => regenerationTime hd lam l (m + 1) ωz.2)
        ((Regeneration.measurable_regenerationTime _ _ _ _ _).comp measurable_snd)
        (a * lam ^ 2) B (mul_nonneg ha (sq_nonneg lam)) t hmoment

/-- A geometric cycle moment has precisely the exponential cycle dependence
allowed in the phase-error statement. -/
theorem geometric_cycle_bound (M S : ℝ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, S * M ^ (m + 1) ≤ C * Real.exp (C * m) := by
  let C := max 1 (max (S * M) (Real.log M))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hSM : S * M ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hlog : Real.log M ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, fun m => ?_⟩
  calc
    S * M ^ (m + 1) = (S * M) * Real.exp ((m : ℝ) * Real.log M) := by
      rw [Real.exp_nat_mul, Real.exp_log hM, pow_succ]
      ring
    _ ≤ C * Real.exp ((m : ℝ) * Real.log M) :=
      mul_le_mul_of_nonneg_right hSM (Real.exp_pos _).le
    _ ≤ C * Real.exp (C * m) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)

/-- The supplied renewal theorem produces cycle-window tails uniformly in
the force and the cycle count, with constants selected after `l` and `δ`. -/
theorem renewal_cycle_tails (hren : node_rt_u3A_renewalStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ (m : ℕ) (t : ℝ≥0),
      regenerationConditionedLaw hd Q lam l K hK.1 hD
        {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
          (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} ≤
        ENNReal.ofReal (C * Real.exp (C * m - a * lam ^ 2 * (t : ℝ))) := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨_, _, a, M, _, _, ha, hM, hmoment⟩ := hren' l hl δ hδ₀ hδ₁
  obtain ⟨C, hC, hcycle⟩ := geometric_cycle_bound M 1 hM
  refine ⟨a, C, ha, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD m t
  have htail := regeneration_cycle_tail_of_moment d hd lam l a (M ^ (m + 1)) ha.le m
    (regenerationConditionedLaw hd Q lam l K hK.1 hD)
    ((hmoment Q lam h₀ h₁ P K hK hD).2.1 (m + 1)) t
  apply htail.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (C * Real.exp (C * m)) * Real.exp (-a * lam ^ 2 * (t : ℝ)) :=
      mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hcycle m)
        (Real.exp_pos _).le
    _ = _ := by simp only [sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

/-- Exponential cycle moments control the literal terminal-cycle remainder
for bounded observations, without any change to its defining event. -/
theorem bounded_regeneration_cycle_remainder (d : ℕ) (hd : 2 ≤ d)
    (lam l a B N : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B) (hN : 0 ≤ N) (m : ℕ)
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d))
    (hmoment : (∫⁻ ωz, if regenerationTime hd lam l (m + 1) ωz.2 = ⊤ then ⊤ else
      ENNReal.ofReal (Real.exp (a * lam ^ 2 *
        (regenerationTime hd lam l (m + 1) ωz.2).toReal)) ∂μ) ≤ ENNReal.ofReal B)
    (G : FieldPair d → ℝ) (hG : ∀ ω, |G ω| ≤ N) (t : ℝ≥0) :
    |∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
        N * B * Real.exp (-a * lam ^ 2 * (t : ℝ)) := by
  have htail := regeneration_cycle_tail_of_moment d hd lam l a B ha m μ hmoment t
  have hfinite := htail.trans_lt ENNReal.ofReal_lt_top
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
  rw [ENNReal.toReal_ofReal (mul_nonneg hB (Real.exp_pos _).le)] at hreal
  have hint := norm_setIntegral_le_of_norm_le_const hfinite
    (fun ωz _ => (show ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ≤ N from
      by simpa only [Real.norm_eq_abs] using hG _))
  calc
    _ ≤ N * μ.real {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} := by
      simpa only [Real.norm_eq_abs] using hint
    _ ≤ N * (B * Real.exp (-a * lam ^ 2 * (t : ℝ))) :=
      mul_le_mul_of_nonneg_left hreal hN
    _ = _ := (mul_assoc _ _ _).symm

/-- The actual terminal-cycle observable satisfies the phase-error estimates
for uniformly bounded local observations. The threshold is structural and all
other constants precede the environment, force, support, cycle and observation.
This bounded-observable theorem does not assert the target `MemLp` estimate. -/
theorem bounded_regeneration_phase_error
    (hmren : node_rt_u3A_m_u2D_renewalStmt) (hren : node_rt_u3A_renewalStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ (A : ℝ) (m : ℕ), l ≤ A → 1 ≤ m → 10 * (m : ℝ) * l - l - A ≥ -2 * l →
    ∀ N : ℝ, 0 ≤ N → ∀ G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    (∀ ω, |G ω| ≤ N) →
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
    (∀ t : ℝ≥0, |rm t| ≤ C * Real.exp (C * m - c * lam ^ 2 * (t : ℝ)) * N) ∧
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun j : ℕ => rm (s + j * Δ)) ∧
      |Hm s| ≤ C * Real.exp (C * m) * N ∧
      ∀ j : ℕ,
        hm (s + j * Δ) = rm (s + j * Δ) +
          ∑ n ∈ Finset.range (j + 1), pn n * hm (s + (j - n : ℕ) * Δ) ∧
        hm (s + j * Δ) - Hm s =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a : ℕ, EinsteinFull.latticeConvolutionPower pn a (j - n)) - mean⁻¹) *
              rm (s + n * Δ)) - mean⁻¹ * ∑' n : ℕ, rm (s + (j + 1 + n : ℕ) * Δ) ∧
        |hm (s + j * Δ) - Hm s| ≤ C * Real.exp (C * m - c * j) * N := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  have hlpos : 0 < l := hl₀.trans_le hl
  have hsepl : r₀ < 2 * l := hsep.trans_le (by linarith only [hl])
  obtain ⟨c₁, C₁, a, M, hc₁, hC₁, ha, hM, hren''⟩ := hren' l hl δ hδ₀ hδ₁
  obtain ⟨C₀, hC₀, hcycle⟩ := geometric_cycle_bound M 1 hM
  obtain ⟨c, D, hc, hDpos, hest⟩ :=
    renewal_phase_error_on_lattice_uniform C₁ c₁ a C₀ hC₁ hc₁ ha hC₀
  let C := max C₀ D
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hDC : D ≤ C := le_max_right _ _
  have hC : 0 < C := hC₀.trans_le hC₀C
  refine ⟨min c a, C, lt_min hc ha, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD A m _hA hmpos hsupport N hN G hG hGb
  dsimp only
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let mean := ∑' n : ℕ, (n : ℝ) * pn n
  let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
    (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  have hactual := hren'' Q lam h₀ h₁ P K hK hD
  have hU : ∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower pn j n) - mean⁻¹| ≤
      C₁ * Real.exp (-c₁ * n) := by
    simpa only [mean, pn, mul_comm] using hactual.1
  have hp : pn 0 = 0 := regenerationLatticeMass_zero hd Q lam l h₀ hlpos K hK.1 hD
  have hΔ : lam ^ 2 * (Δ : ℝ) = 1 := by
    dsimp only [Δ, Regeneration.Renewal.regenDelta]
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
    exact mul_inv_cancel₀ (pow_ne_zero 2 h₀.ne')
  have hr : ∀ t : ℝ≥0, |rm t| ≤ C₀ * Real.exp (C₀ * m - a * lam ^ 2 * (t : ℝ)) * N := by
    intro t
    have hmoment := hactual.2.1 (m + 1)
    have hb := bounded_regeneration_cycle_remainder d hd lam l a (M ^ (m + 1)) N
      ha.le (pow_nonneg hM.le _) hN m ν hmoment G hGb t
    have hpow : M ^ (m + 1) ≤ C₀ * Real.exp (C₀ * m) := by
      simpa only [one_mul] using hcycle m
    calc |rm t| ≤ N * M ^ (m + 1) * Real.exp (-a * lam ^ 2 * (t : ℝ)) := hb
      _ ≤ N * (C₀ * Real.exp (C₀ * m)) * Real.exp (-a * lam ^ 2 * (t : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hN) (Real.exp_pos _).le
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]; ring
  have hh := m_renewal_eq_of_support hmren d hd Λ₀ r₀ l δ hlpos hsepl hδ₀ hδ₁
    Q lam h₀ h₁ P K hK hD A m hmpos hsupport G hG ⟨N, hGb⟩
  refine ⟨?_, ?_⟩
  · intro t
    apply (hr t).trans
    apply mul_le_mul_of_nonneg_right _ hN
    apply mul_le_mul hC₀C _ (Real.exp_pos _).le hC.le
    apply Real.exp_le_exp.mpr
    have hcm := mul_le_mul_of_nonneg_right hC₀C (Nat.cast_nonneg m)
    have hrate := mul_le_mul_of_nonneg_right (min_le_right c a)
      (mul_nonneg (sq_nonneg lam) t.coe_nonneg)
    nlinarith only [hcm, hrate]
  · intro s hs
    obtain ⟨hrs, hlim, herr⟩ := hest pn mean hp hU lam Δ hΔ m N hN hm rm hr hh s hs
    refine ⟨hrs, ?_, ?_⟩
    · apply hlim.trans
      apply mul_le_mul_of_nonneg_right _ hN
      exact mul_le_mul hDC (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hDC (Nat.cast_nonneg m))) (Real.exp_pos _).le hC.le
    · intro j
      obtain ⟨hrec, hid, herror⟩ := herr j
      refine ⟨hrec, hid, herror.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ hN
      apply mul_le_mul hDC _ (Real.exp_pos _).le hC.le
      apply Real.exp_le_exp.mpr
      have hcm := mul_le_mul_of_nonneg_right hDC (Nat.cast_nonneg m)
      have hrate := mul_le_mul_of_nonneg_right (min_le_left c a) (Nat.cast_nonneg j)
      linarith only [hcm, hrate]

/-- The supplied remainder theorem gives integrability of every translated
`MemLp` observation under both actual path laws at all finite times. Taking
`B = b = 1`, the whole sample space and `J = lam²*t` keeps the threshold
structural; no time-dependent tail constants enter its choice. -/
theorem remainder_moment_translated_integrable
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ G : FieldPair d → ℝ, Measurable G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) → ∀ t : ℝ≥0,
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      Integrable (fun ωz => G (translate (ωz.2.1 t) (reduce ωz.1))) μ := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, _hc, _hC, hrem'⟩ :=
    hrem d hd Λ₀ r₀ 1 1 (by norm_num) (by norm_num)
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD G hG hLp t μ hμ
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  letI : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hprob : Regeneration.annealedCoupledLaw Q.measure K Set.univ ≤
      ENNReal.ofReal (1 * Real.exp (1 * (lam ^ 2 * (t : ℝ)) -
        1 * lam ^ 2 * (t : ℝ))) := by simp
  have hint := (hrem' Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun _ => 1) G measurable_const hG (memLp_const 1) hLp
    (lam ^ 2 * (t : ℝ)) t Set.univ (mul_nonneg (sq_nonneg lam) t.coe_nonneg)
    MeasurableSet.univ hprob μ hμ).1
  simpa only [one_mul, integrableOn_univ] using hint

/-- Clamping an integrable real observation to expanding symmetric intervals
commutes with integration on any event. -/
theorem tendsto_setIntegral_clamp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ) (s : Set α) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x in s, max (-(n : ℝ)) (min (n : ℝ) (f x)) ∂μ)
      Filter.atTop (𝓝 (∫ x in s, f x ∂μ)) := by
  have hfi : Integrable f (μ.restrict s) := hf.integrableOn
  apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
  · intro n
    exact (continuous_const.max (continuous_const.min continuous_id)).comp_aestronglyMeasurable
      hfi.aestronglyMeasurable
  · exact hfi.abs
  · intro n
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      refine abs_le.mpr ⟨?_, ?_⟩
      · exact le_trans (le_min
          ((neg_nonpos.mpr (abs_nonneg (f x))).trans (Nat.cast_nonneg n))
          (neg_abs_le (f x))) (le_max_right _ _)
      · exact max_le
          ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (abs_nonneg (f x)))
          ((min_le_right _ _).trans (le_abs_self _)))
  · exact Filter.Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop).eventually
          (Filter.eventually_ge_atTop |f x|)] with n hn
      rw [min_eq_right ((le_abs_self _).trans hn), max_eq_right]
      exact (neg_le_neg hn).trans (neg_abs_le _))

/-- The bounded renewal identity extends to local `MemLp` observations.
The exponent and structural threshold come from V1 with fixed tail constants. -/
theorem m_renewal_eq_memLp
    (hmren : node_rt_u3A_m_u2D_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ) (m : ℕ), 1 ≤ m →
      10 * (m : ℝ) * l - l - A ≥ -2 * l →
    ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let h := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    ∀ t : ℝ≥0, h t = r t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * h (t - n * Δ) := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, p, hl₀, hsep, hp, hInt⟩ :=
    remainder_moment_translated_integrable hrem d hd Λ₀ r₀
  refine ⟨l₀, p, hl₀, hsep, hp, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD A m hm hs G hG hLp
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let H := fun (F : FieldPair d → ℝ) (t : ℝ≥0) => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    F (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let R := fun (F : FieldPair d → ℝ) (t : ℝ≥0) => ∫ ωz in
    {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    F (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let Gk := fun (n : ℕ) (ω : FieldPair d) => max (-(n : ℝ)) (min (n : ℝ) (G ω))
  have hGk (n : ℕ) :
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] (Gk n) :=
    measurable_const.max (measurable_const.min hG)
  have hb (n : ℕ) : Regeneration.BoundedRealTest (Gk n) := by
    refine ⟨(n : ℝ), fun ω => abs_le.mpr ⟨le_max_left _ _, ?_⟩⟩
    exact max_le
      ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans (Nat.cast_nonneg n)) (min_le_left _ _)
  have hi (t : ℝ≥0) :
      Integrable (fun ωz => G (translate (ωz.2.1 t) (reduce ωz.1))) ν :=
    hInt Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD G
      (hG.mono (Probability.localSigma_le_borel _) le_rfl) hLp t ν (by simp [ν])
  have hH (t : ℝ≥0) : Filter.Tendsto (fun n => H (Gk n) t)
      Filter.atTop (𝓝 (H G t)) :=
    tendsto_setIntegral_clamp ν _ (hi t) _
  have hR (t : ℝ≥0) : Filter.Tendsto (fun n => R (Gk n) t)
      Filter.atTop (𝓝 (R G t)) :=
    tendsto_setIntegral_clamp ν _ (hi t) _
  change ∀ t, H G t = R G t +
    ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * H G (t - n * Δ)
  intro t
  have heq (n : ℕ) : H (Gk n) t = R (Gk n) t +
      ∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H (Gk n) (t - k * Δ) :=
    m_renewal_eq_of_support hmren d hd Λ₀ r₀ l δ (hl₀.trans_le hl)
      (hsep.trans_le (by linarith)) hδ₀ hδ₁ Q lam h₀ h₁ P K hK hD A m hm hs
      (Gk n) (hGk n) (hb n) t
  have hsum : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H (Gk n) (t - k * Δ)) Filter.atTop
      (𝓝 (∑ k ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        pn k * H G (t - k * Δ))) :=
    tendsto_finsetSum (Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1))
      (fun k _ => tendsto_const_nhds.mul (hH (t - k * Δ)))
  exact tendsto_nhds_unique (hH t) (((hR t).add hsum).congr'
    (Filter.Eventually.of_forall (fun n => (heq n).symm)))

/-- V1 converts geometric annealed cycle moments into an `Lp` bound for the
literal terminal-cycle remainder under either law. The tail rate `b` precedes
V1's threshold; the geometric prefactor and base may be chosen afterwards.
This order does not resolve the structural-threshold obstruction SI-13. -/
theorem remainder_moment_cycle_bound
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ b : ℝ), 0 < b →
    ∃ l₀ p c : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < c ∧
    ∀ S M : ℝ, 0 < M → ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ m : ℕ,
      (∫⁻ ωz, if regenerationTime hd lam l (m + 1) ωz.2 = ⊤ then ⊤ else
        ENNReal.ofReal (Real.exp (b * lam ^ 2 *
          (regenerationTime hd lam l (m + 1) ωz.2).toReal))
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
          ENNReal.ofReal (S * M ^ (m + 1)) →
    ∀ G : FieldPair d → ℝ, Measurable G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (t : ℝ≥0) μ,
      μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))) →
      IntegrableOn (fun ωz => G (translate (ωz.2.1 t) (reduce ωz.1)))
        {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
          (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} μ ∧
      |∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
          C * Real.exp (C * m - c * lam ^ 2 * (t : ℝ)) *
            (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ b hb
  obtain ⟨l₀, p, c, C₀, hl₀, hsep, hp, hc, hC₀, hrem'⟩ :=
    hrem d hd Λ₀ r₀ 1 b (by norm_num) hb
  refine ⟨l₀, p, c, hl₀, hsep, hp, hc, ?_⟩
  intro S M hM
  obtain ⟨R, hR, hcycle⟩ := geometric_cycle_bound M S hM
  obtain ⟨C, hC, hcycle'⟩ := geometric_cycle_bound (Real.exp (C₀ * R)) C₀
    (Real.exp_pos _)
  refine ⟨C, hC, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD m hmoment G hG hLp t μ hμ
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let J := R * ((m : ℝ) + 1)
  have hJ : 0 ≤ J := mul_nonneg hR.le (by positivity)
  have hpref : S * M ^ (m + 1) ≤ Real.exp J := by
    calc
      _ ≤ R * Real.exp (R * m) := hcycle m
      _ ≤ Real.exp R * Real.exp (R * m) :=
        mul_le_mul_of_nonneg_right
          ((show R ≤ R + 1 by linarith).trans (Real.add_one_le_exp R))
          (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [J]; ring
  have htail := regeneration_cycle_tail_of_moment d hd lam l b
    (S * M ^ (m + 1)) hb.le m (Regeneration.annealedCoupledLaw Q.measure K) hmoment t
  have hprob : Regeneration.annealedCoupledLaw Q.measure K
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} ≤
      ENNReal.ofReal (1 * Real.exp (1 * J - b * lam ^ 2 * (t : ℝ))) := by
    apply htail.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.exp J * Real.exp (-b * lam ^ 2 * (t : ℝ)) :=
        mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; simp only [one_mul, sub_eq_add_neg, neg_mul]
  have hτ (j : ℕ) : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      regenerationTime hd lam l j ωz.2) :=
    (Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
      (l / lam) (Regeneration.Renewal.forceCoord hd) j).comp measurable_snd
  have hmeas : MeasurableSet {ωz : FieldPair d × Regeneration.CoupledSample d |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2} :=
    (measurableSet_le (hτ m) measurable_const).inter
      (measurableSet_lt measurable_const (hτ (m + 1)))
  have hone : eLpNorm (fun _ : FieldPair d => (1 : ℝ))
      (ENNReal.ofReal p) (reducedLaw Q) = 1 := by
    rw [eLpNorm_const' 1 (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
      ENNReal.ofReal_ne_top]
    simp
  have hout := hrem' Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
    (fun _ => 1) G measurable_const hG (memLp_const 1) hLp J t _ hJ hmeas hprob μ hμ
  refine ⟨by simpa only [one_mul] using hout.1, ?_⟩
  have hbound : |∫ ωz in {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
      C₀ * Real.exp (C₀ * J - c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    simpa only [one_mul, hone, ENNReal.toReal_one, mul_one] using hout.2
  have hpref' : C₀ * Real.exp (C₀ * J) ≤ C * Real.exp (C * m) := by
    calc
      _ = C₀ * (Real.exp (C₀ * R)) ^ (m + 1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        congr 1
        dsimp only [J]
        push_cast
        ring
      _ ≤ _ := hcycle' m
  apply hbound.trans
  calc
    _ = (C₀ * Real.exp (C₀ * J)) * Real.exp (-c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ (C * Real.exp (C * m)) * Real.exp (-c * lam ^ 2 * (t : ℝ)) *
        (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref' (Real.exp_pos _).le) ENNReal.toReal_nonneg
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

/-- An exponential continuous-time envelope makes every phase series absolutely
summable, with an explicit bound on the absolute mass after any lattice index. -/
theorem phase_remainder_absolute_tail (r : ℝ≥0 → ℝ) (C b lam N : ℝ) (m : ℕ)
    (hC : 0 ≤ C) (hb : 0 < b) (hN : 0 ≤ N)
    (Δ : ℝ≥0) (hΔ : lam ^ 2 * (Δ : ℝ) = 1)
    (hr : ∀ t : ℝ≥0, |r t| ≤ C * Real.exp (C * m - b * lam ^ 2 * (t : ℝ)) * N)
    (s : ℝ≥0) :
    Summable (fun n : ℕ => |r (s + n * Δ)|) ∧
      ∀ j : ℕ, (∑' n : ℕ, |r (s + (j + n : ℕ) * Δ)|) ≤
        C * Real.exp (C * m - b * j) * N * (1 - Real.exp (-b))⁻¹ := by
  have hρ : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hρ₀ : 0 ≤ Real.exp (-b) := (Real.exp_pos _).le
  have hgeo := hasSum_geometric_of_lt_one hρ₀ hρ
  have hterm (j n : ℕ) : |r (s + (j + n : ℕ) * Δ)| ≤
      (C * Real.exp (C * m - b * j) * N) * Real.exp (-b) ^ n := by
    calc
      _ ≤ C * Real.exp (C * m - b * (j + n : ℕ)) * N :=
        phase_remainder_bound r C b lam N m hC hb.le hN Δ hΔ hr s (j + n)
      _ = _ := by
        rw [← Real.exp_nat_mul]
        rw [Nat.cast_add]
        rw [show C * m - b * ((j : ℝ) + n) =
          (C * m - b * j) + (n : ℝ) * -b by ring, Real.exp_add]
        ring
  have hs (j : ℕ) : Summable (fun n : ℕ => |r (s + (j + n : ℕ) * Δ)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (hterm j)
      (hgeo.summable.mul_left (C * Real.exp (C * m - b * j) * N))
  refine ⟨by simpa only [Nat.zero_add] using hs 0, fun j => ?_⟩
  have hbound := tsum_of_norm_bounded
    (hgeo.mul_left (C * Real.exp (C * m - b * j) * N))
    (f := fun n : ℕ => |r (s + (j + n : ℕ) * Δ)|)
    (fun n => by simpa only [Real.norm_eq_abs, abs_abs] using hterm j n)
  have hnonneg : 0 ≤ ∑' n : ℕ, |r (s + (j + n : ℕ) * Δ)| :=
    tsum_nonneg (fun _ => abs_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound

/-- The literal terminal-cycle remainder has absolutely convergent phase
series under either path law, and exponentially small omitted tails. The
moment rate still precedes the structural threshold, as required by V1. -/
theorem remainder_moment_phase_absolute_tail
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ b : ℝ), 0 < b →
    ∃ l₀ p c : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < c ∧
    ∀ S M : ℝ, 0 < M → ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ m : ℕ,
      (∫⁻ ωz, if regenerationTime hd lam l (m + 1) ωz.2 = ⊤ then ⊤ else
        ENNReal.ofReal (Real.exp (b * lam ^ 2 *
          (regenerationTime hd lam l (m + 1) ωz.2).toReal))
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
          ENNReal.ofReal (S * M ^ (m + 1)) →
    ∀ G : FieldPair d → ℝ, Measurable G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ μ,
      μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))) →
    let Δ := Regeneration.Renewal.regenDelta lam
    let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
    ∀ s : ℝ≥0, Summable (fun n : ℕ => |rm (s + n * Δ)|) ∧
      ∀ j : ℕ, (∑' n : ℕ, |rm (s + (j + n : ℕ) * Δ)|) ≤
        C * Real.exp (C * m - c * j) * Ng * (1 - Real.exp (-c))⁻¹ := by
  intro d hd Λ₀ r₀ b hb
  obtain ⟨l₀, p, c, hl₀, hsep, hp, hc, hcycle⟩ :=
    remainder_moment_cycle_bound hrem d hd Λ₀ r₀ b hb
  refine ⟨l₀, p, c, hl₀, hsep, hp, hc, ?_⟩
  intro S M hM
  obtain ⟨C, hC, hcycle'⟩ := hcycle S M hM
  refine ⟨C, hC, ?_⟩
  intro Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD m hmoment G hG hLp μ hμ
  let Δ := Regeneration.Renewal.regenDelta lam
  let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
    (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
  let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
  change ∀ s : ℝ≥0, Summable (fun n : ℕ => |rm (s + n * Δ)|) ∧
    ∀ j : ℕ, (∑' n : ℕ, |rm (s + (j + n : ℕ) * Δ)|) ≤
      C * Real.exp (C * m - c * j) * Ng * (1 - Real.exp (-c))⁻¹
  have hΔ : lam ^ 2 * (Δ : ℝ) = 1 := by
    dsimp only [Δ, Regeneration.Renewal.regenDelta]
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
    exact mul_inv_cancel₀ (pow_ne_zero 2 h₀.ne')
  have hr : ∀ t : ℝ≥0, |rm t| ≤
      C * Real.exp (C * m - c * lam ^ 2 * (t : ℝ)) * Ng := by
    intro t
    exact (hcycle' Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD
      m hmoment G hG hLp t μ hμ).2
  exact phase_remainder_absolute_tail rm C c lam Ng m hC.le hc
    ENNReal.toReal_nonneg Δ hΔ hr

/-- The actual `MemLp` renewal equation and cycle-moment tail give the exact
phase-error identity, including its entire infinite tail. The common exponent
and threshold are chosen before the environment, force and observation; V1
still requires the exponential-moment rate before that threshold. -/
theorem m_renewal_phase_identity_memLp
    (hmren : node_rt_u3A_m_u2D_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ b : ℝ), 0 < b →
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ S M : ℝ, 0 < M →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ) (m : ℕ), 1 ≤ m →
      10 * (m : ℝ) * l - l - A ≥ -2 * l →
      (∫⁻ ωz, if regenerationTime hd lam l (m + 1) ωz.2 = ⊤ then ⊤ else
        ENNReal.ofReal (Real.exp (b * lam ^ 2 *
          (regenerationTime hd lam l (m + 1) ωz.2).toReal))
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
          ENNReal.ofReal (S * M ^ (m + 1)) →
    ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' n : ℕ, rm (s + n * Δ)
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun n : ℕ => |rm (s + n * Δ)|) ∧
      Summable (fun n : ℕ => rm (s + n * Δ)) ∧
      ∀ j : ℕ,
        hm (s + j * Δ) = rm (s + j * Δ) +
          ∑ n ∈ Finset.range (j + 1), pn n * hm (s + (j - n : ℕ) * Δ) ∧
        hm (s + j * Δ) - Hm s =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a : ℕ, latticeConvolutionPower pn a (j - n)) - mean⁻¹) *
              rm (s + n * Δ)) - mean⁻¹ * ∑' n : ℕ, rm (s + (j + 1 + n : ℕ) * Δ) := by
  intro d hd Λ₀ r₀ b hb
  obtain ⟨L₀, p₀, hL₀, hsep₀, hp₀, hrenew⟩ :=
    m_renewal_eq_memLp hmren hrem d hd Λ₀ r₀
  obtain ⟨L₁, p₁, c, hL₁, hsep₁, hp₁, hc, htail⟩ :=
    remainder_moment_phase_absolute_tail hrem d hd Λ₀ r₀ b hb
  refine ⟨max L₀ L₁, max p₀ p₁, hL₀.trans_le (le_max_left _ _),
    hsep₀.trans_le (by linarith only [le_max_left L₀ L₁]),
    hp₀.trans (le_max_left _ _), ?_⟩
  intro S M hM Q lam h₀ h₁ l δ hl hδ₀ hδ₁ P K hK hD A m hmpos hsupp hmoment G hG hLp
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hLp₀ : MemLp G (ENNReal.ofReal p₀) (reducedLaw Q) :=
    hLp.mono_exponent (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hLp₁ : MemLp G (ENNReal.ofReal p₁) (reducedLaw Q) :=
    hLp.mono_exponent (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  have hl₀ : L₀ ≤ l := (le_max_left _ _).trans hl
  have hl₁ : L₁ ≤ l := (le_max_right _ _).trans hl
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let mean := ∑' n : ℕ, (n : ℝ) * pn n
  let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
    (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  have hrec : ∀ t : ℝ≥0, hm t = rm t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * hm (t - n * Δ) :=
    hrenew Q lam h₀ h₁ l δ hl₀ hδ₀ hδ₁ P K hK hD A m hmpos hsupp G hG hLp₀
  have hΔ : 0 < Δ := by
    dsimp only [Δ, Regeneration.Renewal.regenDelta]
    exact Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hp : pn 0 = 0 :=
    regenerationLatticeMass_zero hd Q lam l h₀ (hL₀.trans_le hl₀) K hK.1 hD
  obtain ⟨C, hC, htail'⟩ := htail S M hM
  dsimp only
  intro s hs
  have habs : Summable (fun n : ℕ => |rm (s + n * Δ)|) :=
    (htail' Q lam h₀ h₁ l δ hl₁ hδ₀ hδ₁ P K hK hD m hmoment G
      (hG.mono (Probability.localSigma_le_borel _) le_rfl) hLp₁ ν (by simp [ν]) s).1
  have hrs : Summable (fun n : ℕ => rm (s + n * Δ)) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  have hphase := renewal_eq_on_phase pn Δ hΔ hm rm hrec s hs
  refine ⟨habs, hrs, fun j => ⟨hphase j, ?_⟩⟩
  exact renewal_phase_error_identity pn (fun n => hm (s + n * Δ))
    (fun n => rm (s + n * Δ)) mean hp hrs hphase j

/-- Quantitative phase estimates for the actual `MemLp` observations, with
one common exponent and constants uniform in the law, force, cycle count and
observation. The annealed cycle moment is explicit: its rate is chosen before
the threshold supplied by V1, rather than after the regeneration scale. -/
theorem m_renewal_phase_estimates_memLp
    (hmren : node_rt_u3A_m_u2D_renewalStmt) (hren : node_rt_u3A_renewalStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ b : ℝ), 0 < b →
    ∃ l₀ p : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ S M : ℝ, 0 < M → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0)
      (A : ℝ) (m : ℕ), l ≤ A → 1 ≤ m →
      10 * (m : ℝ) * l - l - A ≥ -2 * l →
      (∫⁻ ωz, if regenerationTime hd lam l (m + 1) ωz.2 = ⊤ then ⊤ else
        ENNReal.ofReal (Real.exp (b * lam ^ 2 *
          (regenerationTime hd lam l (m + 1) ωz.2).toReal))
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
          ENNReal.ofReal (S * M ^ (m + 1)) →
    ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' n : ℕ, rm (s + n * Δ)
    (∀ t : ℝ≥0, |rm t| ≤ C * Real.exp (C * m - c * lam ^ 2 * (t : ℝ)) * Ng) ∧
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun n : ℕ => rm (s + n * Δ)) ∧
      |Hm s| ≤ C * Real.exp (C * m) * Ng ∧ ∀ j : ℕ,
        hm (s + j * Δ) = rm (s + j * Δ) +
          ∑ n ∈ Finset.range (j + 1), pn n * hm (s + (j - n : ℕ) * Δ) ∧
        hm (s + j * Δ) - Hm s =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a : ℕ, latticeConvolutionPower pn a (j - n)) - mean⁻¹) *
              rm (s + n * Δ)) - mean⁻¹ * ∑' n : ℕ, rm (s + (j + 1 + n : ℕ) * Δ) ∧
        |hm (s + j * Δ) - Hm s| ≤ C * Real.exp (C * m - c * j) * Ng := by
  intro d hd Λ₀ r₀ b hb
  obtain ⟨L₀, p₀, hL₀, hsep₀, hp₀, hrenew⟩ :=
    m_renewal_eq_memLp hmren hrem d hd Λ₀ r₀
  obtain ⟨L₁, p₁, c₀, hL₁, _hsep₁, _hp₁, hc₀, hcycle⟩ :=
    remainder_moment_cycle_bound hrem d hd Λ₀ r₀ b hb
  obtain ⟨L₂, _hL₂, _hsep₂, hren'⟩ := hren d hd Λ₀ r₀
  refine ⟨max L₀ (max L₁ L₂), max p₀ p₁,
    hL₀.trans_le (le_max_left _ _),
    hsep₀.trans_le (by linarith only [le_max_left L₀ (max L₁ L₂)]),
    hp₀.trans (le_max_left _ _), ?_⟩
  intro l hl δ hδ₀ hδ₁ S M hM
  have hl₀ : L₀ ≤ l := (le_max_left _ _).trans hl
  have hl₁ : L₁ ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hl₂ : L₂ ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  obtain ⟨c₁, C₁, _a, _M, hc₁, hC₁, _ha, _hM, hren''⟩ :=
    hren' l hl₂ δ hδ₀ hδ₁
  obtain ⟨C₀, hC₀, hcycle'⟩ := hcycle S M hM
  obtain ⟨c, D, hc, hDpos, hest⟩ :=
    renewal_phase_error_on_lattice_uniform C₁ c₁ c₀ C₀ hC₁ hc₁ hc₀ hC₀
  let C := max C₀ D
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hDC : D ≤ C := le_max_right _ _
  have hC : 0 < C := hC₀.trans_le hC₀C
  refine ⟨min c c₀, C, lt_min hc hc₀, hC, ?_⟩
  intro Q lam h₀ h₁ P K hK hD A m _hA hmpos hsupp hmoment G hG hLp
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hLp₀ : MemLp G (ENNReal.ofReal p₀) (reducedLaw Q) :=
    hLp.mono_exponent (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hLp₁ : MemLp G (ENNReal.ofReal p₁) (reducedLaw Q) :=
    hLp.mono_exponent (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  let Ng := (eLpNorm G (ENNReal.ofReal (max p₀ p₁)) (reducedLaw Q)).toReal
  have hNg : (eLpNorm G (ENNReal.ofReal p₁) (reducedLaw Q)).toReal ≤ Ng :=
    ENNReal.toReal_mono hLp.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le
        (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Regeneration.Renewal.regenDelta lam
  let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
  let mean := ∑' n : ℕ, (n : ℝ) * pn n
  let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
    regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
    (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
    G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
  have hactual := hren'' Q lam h₀ h₁ P K hK hD
  have hU : ∀ n : ℕ, |(∑' a : ℕ, latticeConvolutionPower pn a n) - mean⁻¹| ≤
      C₁ * Real.exp (-c₁ * n) := by
    simpa only [pn, mean, mul_comm] using hactual.1
  have hp : pn 0 = 0 :=
    regenerationLatticeMass_zero hd Q lam l h₀ (hL₀.trans_le hl₀) K hK.1 hD
  have hΔ : lam ^ 2 * (Δ : ℝ) = 1 := by
    dsimp only [Δ, Regeneration.Renewal.regenDelta]
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
    exact mul_inv_cancel₀ (pow_ne_zero 2 h₀.ne')
  have hr : ∀ t : ℝ≥0, |rm t| ≤
      C₀ * Real.exp (C₀ * m - c₀ * lam ^ 2 * (t : ℝ)) * Ng := by
    intro t
    have hbnd := (hcycle' Q lam h₀ h₁ l δ hl₁ hδ₀ hδ₁ P K hK hD
      m hmoment G (hG.mono (Probability.localSigma_le_borel _) le_rfl)
      hLp₁ t ν (by simp [ν])).2
    exact hbnd.trans (mul_le_mul_of_nonneg_left hNg
      (mul_nonneg hC₀.le (Real.exp_pos _).le))
  have hh : ∀ t : ℝ≥0, hm t = rm t +
      ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1), pn n * hm (t - n * Δ) :=
    hrenew Q lam h₀ h₁ l δ hl₀ hδ₀ hδ₁ P K hK hD A m hmpos hsupp G hG hLp₀
  dsimp only
  refine ⟨?_, ?_⟩
  · intro t
    apply (hr t).trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply mul_le_mul hC₀C _ (Real.exp_pos _).le hC.le
    apply Real.exp_le_exp.mpr
    have hcm := mul_le_mul_of_nonneg_right hC₀C (Nat.cast_nonneg m)
    have hrate := mul_le_mul_of_nonneg_right (min_le_right c c₀)
      (mul_nonneg (sq_nonneg lam) t.coe_nonneg)
    nlinarith only [hcm, hrate]
  · intro s hs
    obtain ⟨hrs, hlim, herr⟩ := hest pn mean hp hU lam Δ hΔ m Ng
      ENNReal.toReal_nonneg hm rm hr hh s hs
    refine ⟨hrs, ?_, ?_⟩
    · apply hlim.trans
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      exact mul_le_mul hDC (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hDC (Nat.cast_nonneg m))) (Real.exp_pos _).le hC.le
    · intro j
      obtain ⟨hrec, hid, herror⟩ := herr j
      refine ⟨hrec, hid, herror.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply mul_le_mul hDC _ (Real.exp_pos _).le hC.le
      apply Real.exp_le_exp.mpr
      have hcm := mul_le_mul_of_nonneg_right hDC (Nat.cast_nonneg m)
      have hrate := mul_le_mul_of_nonneg_right (min_le_left c c₀) (Nat.cast_nonneg j)
      linarith only [hcm, hrate]

/-- Lowering the rate decreases an extended-time exponential moment. The
infinite-time branch remains infinite at every rate, so no finiteness or
measurability premise is needed for this comparison. -/
theorem exponential_time_moment_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ≥0∞) (a b : ℝ) (hba : b ≤ a) :
    (∫⁻ ω, if T ω = ⊤ then ⊤ else
      ENNReal.ofReal (Real.exp (b * (T ω).toReal)) ∂μ) ≤
    ∫⁻ ω, if T ω = ⊤ then ⊤ else
      ENNReal.ofReal (Real.exp (a * (T ω).toReal)) ∂μ := by
  apply lintegral_mono
  intro ω
  by_cases htop : T ω = ⊤
  · simp only [htop, ↓reduceIte, le_refl]
  · simp only [htop, ↓reduceIte]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hba ENNReal.toReal_nonneg))

/-- The literal renewal theorem controls both actual path-law exponential
moments at every smaller rate, with the same prefactors. The available rate
is still chosen after `l` and `δ`; this comparison does not interchange the
rate and threshold quantifiers required by the phase-error reduction. -/
theorem renewal_moments_at_smaller_rates (hren : node_rt_u3A_renewalStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a C M : ℝ, 0 < a ∧ 0 < C ∧ 0 < M ∧
    ∀ b : ℝ, b ≤ a →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ j : ℕ,
      (∫⁻ ωz, if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
        ENNReal.ofReal (Real.exp (b * lam ^ 2 *
          (regenerationTime hd lam l j ωz.2).toReal))
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (M ^ j) ∧
      (∫⁻ ωz, if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
        ENNReal.ofReal (Real.exp (b * lam ^ 2 *
          (regenerationTime hd lam l j ωz.2).toReal))
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
          ENNReal.ofReal (C * M ^ j) := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hsep, hren'⟩ := hren d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨_c, C, a, M, _hc, hC, ha, hM, hactual⟩ := hren' l hl δ hδ₀ hδ₁
  refine ⟨a, C, M, ha, hC, hM, ?_⟩
  intro b hba Q lam h₀ h₁ P K hK hD j
  have hrate : b * lam ^ 2 ≤ a * lam ^ 2 :=
    mul_le_mul_of_nonneg_right hba (sq_nonneg lam)
  have hmom := (hactual Q lam h₀ h₁ P K hK hD).2
  constructor
  · exact (exponential_time_moment_mono
      (regenerationConditionedLaw hd Q lam l K hK.1 hD)
      (fun ωz => regenerationTime hd lam l j ωz.2)
      (a * lam ^ 2) (b * lam ^ 2) hrate).trans (hmom.1 j)
  · exact (exponential_time_moment_mono
      (Regeneration.annealedCoupledLaw Q.measure K)
      (fun ωz => regenerationTime hd lam l j ωz.2)
      (a * lam ^ 2) (b * lam ^ 2) hrate).trans (hmom.2 j)

end EinsteinFull.Blueprint
