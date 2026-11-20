import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Iteration of slab energy estimates

The finite iteration in Gantert–Mathieu–Piatnitski, Lemma 4.4, turns a
weighted energy recurrence into a bound below the reciprocal slab width.
-/

open Filter
open scoped Topology

namespace EinsteinFull.Regeneration

/-- Iterating an affine contraction bounds the accumulated error and initial energy. -/
theorem energy_le_of_affine_contraction (E : ℕ → ℝ) (A q : ℝ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2)
    (n : ℕ) (hstep : ∀ j < n, E (j + 1) ≤ A + q * E j) :
    E n ≤ 2 * A + q ^ n * E 0 := by
  induction n with
  | zero => simp only [pow_zero, one_mul]; linarith
  | succ n ih =>
      calc
        E (n + 1) ≤ A + q * E n := hstep n (Nat.lt_succ_self n)
        _ ≤ A + q * (2 * A + q ^ n * E 0) :=
          by
            have hin := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
            linarith [mul_le_mul_of_nonneg_left hin hq]
        _ ≤ 2 * A + q ^ (n + 1) * E 0 := by
          rw [pow_succ]
          nlinarith

/-- A polynomial times a strictly decaying exponential tends to zero. -/
theorem tendsto_pow_mul_exp_neg_rate (n : ℕ) (α : ℝ) (hα : 0 < α) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-(α * x))) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) α hα
  simpa only [Real.rpow_natCast, neg_mul] using h

/-- After sufficiently many slab-energy steps, the upper envelope is `o(1 / x)`. -/
theorem tendsto_slab_energy_envelope (A C D α β : ℝ) (n : ℕ)
    (hα : 0 < α) (hdecay : 0 < (n : ℝ) * α - β) :
    Tendsto (fun x : ℝ => x * (2 * A * Real.exp (-(α * x)) +
      (C * x ^ 2 * Real.exp (-(α * x))) ^ n * D * Real.exp (β * x))) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun x : ℝ => (2 * A) * (x ^ 1 * Real.exp (-(α * x))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_mul_exp_neg_rate 1 α hα).const_mul (2 * A)
  have hlast : Tendsto (fun x : ℝ => (C ^ n * D) *
      (x ^ (2 * n + 1) * Real.exp (-(((n : ℝ) * α - β) * x)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_mul_exp_neg_rate (2 * n + 1) ((n : ℝ) * α - β) hdecay).const_mul (C ^ n * D)
  have hsum := hfirst.add hlast
  simp only [zero_add] at hsum
  apply hsum.congr
  intro x
  have hexp : Real.exp (-(α * x)) ^ n * Real.exp (β * x) =
      Real.exp (-(((n : ℝ) * α - β) * x)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, ← pow_mul, pow_add]
  simp only [pow_one]
  rw [← hexp]
  ring

/-- A sufficiently wide slab makes the iterated upper energy smaller than `c / L`. -/
theorem exists_slab_width_of_energy_recurrence (A C D α β c : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hα : 0 < α) (hc : 0 < c)
    (hdecay : 0 < (n : ℝ) * α - β) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ E : ℕ → ℝ,
      (∀ j < n, E (j + 1) ≤ A * Real.exp (-(α * L)) +
        (C * L ^ 2 * Real.exp (-(α * L))) * E j) →
      E 0 ≤ D * Real.exp (β * L) → L * E n < c := by
  have hq : Tendsto (fun x : ℝ => C * (x ^ 2 * Real.exp (-(α * x))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_mul_exp_neg_rate 2 α hα).const_mul C
  have hqsmall : ∀ᶠ L : ℝ in atTop, C * L ^ 2 * Real.exp (-(α * L)) ≤ 1 / 2 := by
    filter_upwards [hq.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with L hL
    nlinarith
  have henv := tendsto_slab_energy_envelope A C D α β n hα hdecay
  have hsmall : ∀ᶠ L : ℝ in atTop, L * (2 * A * Real.exp (-(α * L)) +
      (C * L ^ 2 * Real.exp (-(α * L))) ^ n * D * Real.exp (β * L)) < c :=
    henv.eventually (eventually_lt_nhds hc)
  have hall : ∀ᶠ L : ℝ in atTop, 0 ≤ L ∧
      C * L ^ 2 * Real.exp (-(α * L)) ≤ 1 / 2 ∧
      L * (2 * A * Real.exp (-(α * L)) +
        (C * L ^ 2 * Real.exp (-(α * L))) ^ n * D * Real.exp (β * L)) < c := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hqsmall, hsmall] with L hL hqL hs
    exact ⟨hL, hqL, hs⟩
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hall
  refine ⟨L₀, ?_⟩
  intro L hL E hstep hinit
  obtain ⟨hLnonneg, hqL, hs⟩ := hL₀ L hL
  have hqnonneg : 0 ≤ C * L ^ 2 * Real.exp (-(α * L)) := by positivity
  have hbound := energy_le_of_affine_contraction E (A * Real.exp (-(α * L)))
    (C * L ^ 2 * Real.exp (-(α * L))) (by positivity) hqnonneg hqL n hstep
  have hinit' := mul_le_mul_of_nonneg_left hinit (pow_nonneg hqnonneg n)
  have hfinal : E n ≤ 2 * A * Real.exp (-(α * L)) +
      (C * L ^ 2 * Real.exp (-(α * L))) ^ n * D * Real.exp (β * L) := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hfinal hLnonneg).trans_lt hs

/-- The `2d` steps and exponential rates in GMP (4.19)–(4.21) contradict a `c / L` lower bound. -/
theorem exists_slab_width_of_gmp_energy_recurrence (d : ℕ) (hd : 0 < d)
    (A C D c : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ E : ℕ → ℝ,
      (∀ j < 2 * d, E (j + 1) ≤ A * Real.exp (-(L / d)) +
        (C * L ^ 2 * Real.exp (-(L / d))) * E j) →
      E 0 ≤ D * Real.exp (((2 * d - 1) / d) * L) → L * E (2 * d) < c := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hα : 0 < 1 / (d : ℝ) := by positivity
  have hdecay : 0 < ((2 * d : ℕ) : ℝ) * (1 / (d : ℝ)) -
      ((2 * (d : ℝ) - 1) / d) := by
    push_cast
    have heq : 2 * (d : ℝ) * (1 / d) - (2 * (d : ℝ) - 1) / d = 1 / d := by
      field_simp
      ring
    rw [heq]
    positivity
  obtain ⟨L₀, hL₀⟩ := exists_slab_width_of_energy_recurrence A C D
    (1 / (d : ℝ)) ((2 * (d : ℝ) - 1) / d) c (2 * d) hA hC hα hc hdecay
  refine ⟨L₀, ?_⟩
  intro L hL E hstep hinit
  apply hL₀ L hL E
  · intro j hj
    simpa [div_eq_mul_inv, mul_comm] using hstep j hj
  · exact hinit

end EinsteinFull.Regeneration
