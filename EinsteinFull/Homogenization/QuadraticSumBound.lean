import EinsteinFull.Homogenization.SourceResponseDecrementSummability

/-!
# Finite-dimensional bounds for nonnegative quadratic functions

A nonnegative quadratic function is bounded on a coordinate box by a finite
sum of its values on the coordinate vectors. The response-energy decrements
in Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 2, have this form.
-/

namespace EinsteinFull.Homogenization

/-- A nonnegative function satisfying the parallelogram identity is bounded on
finite sums in terms of its values on the summands. -/
theorem quadratic_sum_le {ι M : Type*} [AddCommGroup M]
    (Q : M → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hpar : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (s : Finset ι) (v : ι → M) :
    Q (∑ i ∈ s, v i) ≤ (2 : ℝ) ^ s.card * ∑ i ∈ s, Q (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero := hpar (0 : M) 0
      simp only [zero_add, sub_self] at hzero
      simp only [Finset.sum_empty, Finset.card_empty, pow_zero, mul_zero]
      linarith
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      have h := hpar (v a) (∑ i ∈ s, v i)
      have hn := hQ (v a - ∑ i ∈ s, v i)
      have hq := hQ (v a)
      have hp : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hq]

/-- A nonnegative quadratic function on a finite coordinate space is bounded
on the unit coordinate box by a sum of its values at coordinate vectors. -/
theorem quadratic_le_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ℝ) → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hpar : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hsmul : ∀ (c : ℝ) x, Q (c • x) = c ^ 2 * Q x)
    (x : ι → ℝ) (hx : ∀ i, x i ^ 2 ≤ 1) :
    Q x ≤ (2 : ℝ) ^ Fintype.card ι * ∑ i : ι, Q (Pi.single i 1) := by
  have hxsum : (∑ i : ι, Pi.single i (x i)) = x := Finset.univ_sum_single x
  have h := quadratic_sum_le Q hQ hpar Finset.univ (fun i => Pi.single i (x i))
  rw [hxsum, Finset.card_univ] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply Finset.sum_le_sum
  intro i _
  have hs : Pi.single i (x i) = x i • Pi.single i (1 : ℝ) := by
    ext j
    by_cases hij : i = j <;> simp [hij]
  rw [hs, hsmul]
  nlinarith [hQ (Pi.single i 1), hx i]

end EinsteinFull.Homogenization
