import EinsteinRelation.Sharpness.CoefficientDivergenceJet
import EinsteinRelation.Sharpness.DensityBounds
import EinsteinRelation.Sharpness.ScaledSeedDerivatives
import EinsteinRelation.Sharpness.SeedField
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! # Uniform density parameter for the scaled canonical seed

Source: `paper/main.tex`, lines 1225–1231. The clock density `μ = densityField i δ ψ` satisfies
`3/4 ≤ μ ≤ 5/4` once `δ` is fixed, as the sentence at line 1231 requires.
Here `ψ = ε * seedField d W`.

The divergence of the first coefficient column is the explicit second-jet expression of
`divergence_coefficientField_column_eq_jet`. Under the Euclidean gradient bound `‖∇ψ‖ ≤ 1/4`,
every term of that expression is bounded by the common second-jet bound `M` of
`exists_uniform_scaled_seedField_third_jet_bound`. The resulting constant `6 * (d * M)` does not
depend on the sample or the point, so `exists_uniform_densityField_parameter` gives one `δ > 0`
before all samples and points.

No divergence bound, density positivity, or random-field derivative premise is assumed: the only
analytic input is the actual gradient bound and the proved jet bound.
-/

open scoped BigOperators

namespace EinsteinRelation.Sharpness

/-- Each coordinate of a vector is bounded by its Euclidean norm. -/
private lemma densityJet_abs_coord_le {d : ℕ} (k : Fin d) (x : Vec d) :
    |x k| ≤ euclideanNorm x := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [pow_two]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
    (Finset.mem_univ k)

/-- A finite sum of `d` terms, each bounded by `M`, is bounded by `d * M`. -/
private lemma densityJet_abs_sum_le {d : ℕ} (f : Fin d → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) :
    |∑ k, f k| ≤ (d : ℝ) * M := by
  calc |∑ k, f k| ≤ ∑ k, |f k| := Finset.abs_sum_le_sum_abs f Finset.univ
    _ ≤ ∑ _k : Fin d, M := Finset.sum_le_sum fun k _ => hM k
    _ = (d : ℝ) * M := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Real-variable estimate for the second-jet expression of the divergence. If `|g k| ≤ 1/4`,
then `1 + g i ≥ 3/4`, so the reciprocal `(1 + g i)⁻¹` lies in `[0, 4/3]`. The three terms are
bounded by `d * M`, `(8/3) * d * M`, and `(16/9) * d * M`, and their total is at most
`6 * (d * M)`. The constants are generous on purpose; no sharp constant is needed. -/
private lemma densityJet_expression_le {d : ℕ} (i : Fin d) (M : ℝ) (hM : 0 ≤ M)
    (g : Vec d) (P Q : Fin d → ℝ) (R : ℝ)
    (hg : ∀ k, |g k| ≤ (1 / 4 : ℝ)) (hP : ∀ k, |P k| ≤ M) (hQ : ∀ k, |Q k| ≤ M)
    (hR : |R| ≤ M) :
    |-(∑ k, P k) + (2 * ∑ k, g k * Q k) / (1 + g i) -
        euclideanSq g * R / (1 + g i) ^ 2| ≤ 6 * ((d : ℝ) * M) := by
  have hdM : 0 ≤ (d : ℝ) * M := mul_nonneg (Nat.cast_nonneg d) hM
  have hL : (3 / 4 : ℝ) ≤ 1 + g i := by
    have h := (abs_le.mp (hg i)).1
    linarith
  have hL0 : (0 : ℝ) < 1 + g i := by linarith
  have hu0 : (0 : ℝ) ≤ (1 + g i)⁻¹ := inv_nonneg.mpr hL0.le
  have hu1 : (1 + g i)⁻¹ ≤ (4 / 3 : ℝ) := by
    have hmul : (1 + g i) * (1 + g i)⁻¹ = 1 := mul_inv_cancel₀ hL0.ne'
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) hu0]
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ (4 / 3 : ℝ) →
      |-(∑ k, P k) + (2 * ∑ k, g k * Q k) * u - euclideanSq g * R * u ^ 2|
        ≤ 6 * ((d : ℝ) * M) := by
    intro u hu0' hu1'
    have hsumP : |∑ k, P k| ≤ (d : ℝ) * M := densityJet_abs_sum_le P M hP
    have hG : |∑ k, g k * Q k| ≤ (d : ℝ) * M := by
      refine densityJet_abs_sum_le (fun k => g k * Q k) M (fun k => ?_)
      show |g k * Q k| ≤ M
      have h1 : |g k| ≤ 1 := by linarith [hg k]
      rw [abs_mul]
      calc |g k| * |Q k| ≤ 1 * M := mul_le_mul h1 (hQ k) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    have hS : |euclideanSq g| ≤ (d : ℝ) := by
      have h : |∑ k, g k * g k| ≤ (d : ℝ) * 1 := by
        refine densityJet_abs_sum_le (fun k => g k * g k) 1 (fun k => ?_)
        show |g k * g k| ≤ 1
        have h1 : |g k| ≤ 1 := by linarith [hg k]
        rw [abs_mul]
        calc |g k| * |g k| ≤ 1 * 1 := mul_le_mul h1 h1 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      rw [mul_one] at h
      exact h
    have hT1 : |-(∑ k, P k)| ≤ (d : ℝ) * M := by
      rw [abs_neg]
      exact hsumP
    have hT2 : |(2 * ∑ k, g k * Q k) * u| ≤ 2 * ((d : ℝ) * M) * (4 / 3) := by
      rw [abs_mul, abs_mul, abs_two]
      have hu_abs : |u| ≤ 4 / 3 := by
        rw [abs_of_nonneg hu0']
        exact hu1'
      exact mul_le_mul (by linarith) hu_abs (abs_nonneg u) (by linarith)
    have hT3 : |euclideanSq g * R * u ^ 2| ≤ (d : ℝ) * M * (16 / 9) := by
      have hu2 : u ^ 2 ≤ (16 / 9 : ℝ) := by
        calc u ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := pow_le_pow_left₀ hu0' hu1' 2
          _ = 16 / 9 := by norm_num
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg u)]
      exact mul_le_mul (mul_le_mul hS hR (abs_nonneg R) (Nat.cast_nonneg d)) hu2
        (sq_nonneg u) hdM
    have ha := abs_le.mp hT1
    have hb := abs_le.mp hT2
    have hc := abs_le.mp hT3
    rw [abs_le]
    constructor
    · linarith [ha.1, hb.1, hc.2]
    · linarith [ha.2, hb.2, hc.1]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow]
  exact key _ hu0 hu1

/-- Under the Euclidean gradient bound `‖∇ψ‖ ≤ 1/4` and a uniform bound `M` on all second
coordinate derivatives of `ψ`, the divergence of the first coefficient column is at most
`6 * (d * M)` at every point. The bound holds at every point `x`, and the constant is independent
of `x`. -/
private lemma densityJet_divergence_bound {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hnorm : ∀ y, euclideanNorm (gradient ψ y) ≤ (1 / 4 : ℝ))
    (hjet2 : ∀ (y : Vec d) (a b : Fin d), |coordinateDerivative a (coordinateDerivative b ψ) y| ≤ M)
    (x : Vec d) :
    |divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x| ≤
      6 * ((d : ℝ) * M) := by
  have hcoord : ∀ y k, |gradient ψ y k| ≤ (1 / 4 : ℝ) := fun y k =>
    (densityJet_abs_coord_le k (gradient ψ y)).trans (hnorm y)
  have hj : ∀ y, jacobianFactor i (gradient ψ y) ≠ 0 := by
    intro y
    have h := (abs_le.mp (hcoord y i)).1
    have hpos : 0 < jacobianFactor i (gradient ψ y) := by
      unfold jacobianFactor
      linarith
    exact hpos.ne'
  rw [divergence_coefficientField_column_eq_jet i ψ hψ hj x]
  exact densityJet_expression_le i M hM (gradient ψ x)
    (fun k => coordinateDerivative k (coordinateDerivative k ψ) x)
    (fun k => coordinateDerivative i (coordinateDerivative k ψ) x)
    (coordinateDerivative i (coordinateDerivative i ψ) x) (hcoord x)
    (fun k => hjet2 x k k) (fun k => hjet2 x i k) (hjet2 x i i)

/-- Source: `paper/main.tex`, lines 1225–1231. For each fixed scale `ε`, if the Euclidean gradient
of the scaled canonical seed is at most `1/4` for every sample and every point, then one
deterministic `δ > 0` gives `3/4 ≤ μ ≤ 5/4` for every sample and every point, where
`μ = densityField i δ (fun y => ε * seedField d W y)`. The constant `δ` is chosen before the sample
`W` and the point `x`. -/
theorem exists_uniform_seedField_density_parameter_of_gradient_bound :
    (∀ {d : ℕ} (i : Fin d) (ε : ℝ),
      (∀ (W : NoiseSample d) (x : Vec d),
        euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (W : NoiseSample d) (x : Vec d),
        (3/4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
        densityField i δ (fun y => ε * seedField d W y) x ≤ (5/4 : ℝ)) := by
  intro d i ε hgrad
  obtain ⟨M, hM, hjet⟩ := exists_uniform_scaled_seedField_third_jet_bound d ε
  have hdM : 0 ≤ (d : ℝ) * M := mul_nonneg (Nat.cast_nonneg d) hM
  have hD : 0 ≤ 6 * ((d : ℝ) * M) := mul_nonneg (by norm_num) hdM
  obtain ⟨δ, hδ, hpar⟩ := exists_uniform_densityField_parameter i (6 * ((d : ℝ) * M)) hD
  refine ⟨δ, hδ, fun W x => ?_⟩
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y => ε * seedField d W y) :=
    ContDiff.mul (contDiff_const (c := ε)) (contDiff_seedField d W)
  have hdiv : ∀ z, |divergence
      (fun y => (coefficientField i (fun w => ε * seedField d W w) y).mulVec (unitVector i)) z| ≤
        6 * ((d : ℝ) * M) := fun z =>
    densityJet_divergence_bound i (fun y => ε * seedField d W y) M hM hψ
      (fun y => hgrad W y) (fun y a b => (hjet W y).2.2.1 a b) z
  exact hpar (fun y => ε * seedField d W y) hdiv x

end EinsteinRelation.Sharpness
