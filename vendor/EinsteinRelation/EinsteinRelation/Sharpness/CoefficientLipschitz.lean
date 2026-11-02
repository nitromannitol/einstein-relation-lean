import EinsteinRelation.TimeChange.Pairing
import EinsteinRelation.Sharpness.MatrixDefs

/-! # Euclidean Lipschitz bound for the sharpness coefficient

`paper/main.tex:1218–1231`, `eq.sharp-map` and `eq.sharp-coefficients`. The coefficient
`a = j B Bᵀ` with `B = inverseCandidate i g` and `j = jacobianFactor i g = 1 + ∂ᵢψ` has the
explicit entry formula

  `a(g) j k = j δⱼₖ - eⱼ gₖ - gⱼ eₖ + j⁻¹ |g|² eⱼ eₖ`,  where `e = unitVector i`.

For `‖g‖ ≤ 1/4` and `‖h‖ ≤ 1/4` every coordinate difference is bounded by `‖g - h‖`, the
factors `j⁻¹` lie in `[0, 4/3]`, and `|j_g⁻¹ - j_h⁻¹| ≤ 2 ‖g - h‖`. The four bounded terms of the
entry difference then give `|a(g) j k - a(h) j k| ≤ 8 ‖g - h‖` in the literal Euclidean norm.
The constant `8` is chosen before `i`, `g`, `h`, `j`, `k`, and does not depend on `d` either.
No Lipschitz or differentiability premise is assumed.
-/

namespace EinsteinRelation.Sharpness

open EinsteinRelation.TimeChange
  (abs_dot_le_euclideanNorm euclideanNorm_add_le euclideanSq_eq_sq_euclideanNorm)

/-! ### Entry formula for the coefficient -/

/-- Transpose of an outer product: `(u ⊗ v)ᵀ = v ⊗ u`. Copy of the private `RankOne` lemma. -/
private theorem coeff_outer_transpose {d : ℕ} (u v : Vec d) :
    (outer u v).transpose = outer v u := by
  ext k l
  simp only [Matrix.transpose_apply, outer]
  ring

/-- Product of outer products: `(u ⊗ v)(w ⊗ x) = (v · w) (u ⊗ x)`. Copy of the private
`RankOne` lemma. -/
private theorem coeff_outer_mul_outer {d : ℕ} (u v w x : Vec d) :
    outer u v * outer w x = dot v w • outer u x := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, outer, dot, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- Expanded form of `B Bᵀ` for `B = 1 - s (e ⊗ g)`, `s = (1 + gᵢ)⁻¹`, `e = unitVector i`.
Copy of the private `RankOne` lemma `inverseCandidate_mul_transpose`. -/
private theorem coeff_candidate_mul_transpose {d : ℕ} (i : Fin d) (g : Vec d) :
    inverseCandidate i g * (inverseCandidate i g).transpose =
      1 - (jacobianFactor i g)⁻¹ • outer (unitVector i) g
        - (jacobianFactor i g)⁻¹ • outer g (unitVector i)
        + ((jacobianFactor i g)⁻¹ * ((jacobianFactor i g)⁻¹ * dot g g)) •
            outer (unitVector i) (unitVector i) := by
  unfold inverseCandidate
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, coeff_outer_transpose]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
    coeff_outer_mul_outer, smul_smul]
  abel

/-- Entrywise formula `a(g) j k = j δⱼₖ - eⱼ gₖ - gⱼ eₖ + j⁻¹ |g|² eⱼ eₖ` for the coefficient,
with `j = 1 + gᵢ`, `e = unitVector i`, `|g|² = dot g g`, when `j ≠ 0`.
Source: `paper/main.tex:1218–1231`, `eq.sharp-coefficients`. -/
private theorem coefficient_entry_eq {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d)
    (hj : jacobianFactor i g ≠ 0) :
    coefficient i g j k = jacobianFactor i g * (1 : Mat d) j k
      - unitVector i j * g k - g j * unitVector i k
      + (jacobianFactor i g)⁻¹ * dot g g * (unitVector i j * unitVector i k) := by
  have hs : (jacobianFactor i g)⁻¹ * jacobianFactor i g = 1 := inv_mul_cancel₀ hj
  unfold coefficient
  rw [coeff_candidate_mul_transpose]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, outer, smul_eq_mul]
  linear_combination (-(unitVector i j * g k + g j * unitVector i k)
    + (jacobianFactor i g)⁻¹ * dot g g * (unitVector i j * unitVector i k)) * hs

/-- Entrywise difference of two coefficients, written as a four-term expression in the
coordinates of `g` and `h`. -/
private theorem coefficient_entry_sub {d : ℕ} (i : Fin d) (g h : Vec d) (j k : Fin d)
    (hg : jacobianFactor i g ≠ 0) (hh : jacobianFactor i h ≠ 0) :
    coefficient i g j k - coefficient i h j k =
      (jacobianFactor i g - jacobianFactor i h) * (1 : Mat d) j k
      - (g k - h k) * unitVector i j - (g j - h j) * unitVector i k
      + ((jacobianFactor i g)⁻¹ * dot g g - (jacobianFactor i h)⁻¹ * dot h h)
        * (unitVector i j * unitVector i k) := by
  rw [coefficient_entry_eq i g j k hg, coefficient_entry_eq i h j k hh]
  ring

/-! ### Coordinate and Euclidean-norm bounds -/

/-- Each coordinate is bounded by the explicit Euclidean norm. -/
private theorem coeff_coord_abs_le {d : ℕ} (i : Fin d) (x : Vec d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [pow_two]
  exact Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

/-- The explicit Euclidean norm is nonnegative. -/
private theorem coeff_euclideanNorm_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclideanNorm x := by
  unfold euclideanNorm
  exact Real.sqrt_nonneg _

/-- A coordinate difference is bounded by the Euclidean norm of the difference. -/
private theorem coeff_diff_coord_abs_le {d : ℕ} (i : Fin d) (g h : Vec d) :
    |g i - h i| ≤ euclideanNorm (g - h) := by
  have h1 := coeff_coord_abs_le i (g - h)
  rwa [Pi.sub_apply] at h1

/-- The difference of the two Jacobian factors is a coordinate difference. -/
private theorem coeff_jf_sub_abs_le {d : ℕ} (i : Fin d) (g h : Vec d) :
    |jacobianFactor i g - jacobianFactor i h| ≤ euclideanNorm (g - h) := by
  have hdiff : jacobianFactor i g - jacobianFactor i h = g i - h i := by
    unfold jacobianFactor
    ring
  rw [hdiff]
  exact coeff_diff_coord_abs_le i g h

/-- Coordinates of a unit vector are bounded by one in absolute value. -/
private theorem coeff_unitVector_abs_le {d : ℕ} (i j : Fin d) : |unitVector i j| ≤ 1 := by
  unfold unitVector
  rw [Pi.single_apply]
  split_ifs <;> norm_num

/-- Products of two coordinates of a unit vector are bounded by one in absolute value. -/
private theorem coeff_unitVector_mul_abs_le {d : ℕ} (i j k : Fin d) :
    |unitVector i j * unitVector i k| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg (unitVector i k)) (coeff_unitVector_abs_le i j)).trans
    (coeff_unitVector_abs_le i k)

/-- Entries of the identity matrix are bounded by one in absolute value. -/
private theorem coeff_one_abs_le {d : ℕ} (j k : Fin d) : |(1 : Mat d) j k| ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> norm_num

/-! ### Real-number product and sum bounds -/

/-- Bound on a product by the product of bounds. -/
private theorem coeff_abs_mul_le {x y D B : ℝ} (hx : |x| ≤ D) (hy : |y| ≤ B) (hD : 0 ≤ D) :
    |x * y| ≤ D * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) hD

/-- Bound on a product where the second factor is bounded by one. -/
private theorem coeff_abs_mul_le_one {x y D : ℝ} (hx : |x| ≤ D) (hy : |y| ≤ 1) :
    |x * y| ≤ D := by
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg x) hy).trans hx

/-- Four-term combination: each term bounded by `D`, except the last by `4 D`, gives `8 D`. -/
private theorem coeff_four_term_abs_le {a b c e D : ℝ} (hD : 0 ≤ D) (ha : |a| ≤ D)
    (hb : |b| ≤ D) (hc : |c| ≤ D) (he : |e| ≤ 4 * D) : |a - b - c + e| ≤ 8 * D := by
  obtain ⟨a1, a2⟩ := abs_le.mp ha
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨c1, c2⟩ := abs_le.mp hc
  obtain ⟨e1, e2⟩ := abs_le.mp he
  rw [abs_le]
  constructor <;> linarith

/-! ### Bounds on the inverse Jacobian factors and the squared norms -/

/-- For `3/4 ≤ x`, the reciprocal lies in `[0, 4/3]`. -/
private theorem coeff_inv_bounds {x : ℝ} (hx : 3 / 4 ≤ x) : 0 ≤ x⁻¹ ∧ x⁻¹ ≤ 4 / 3 := by
  have hpos : 0 < x := by linarith
  have hs : x⁻¹ * x = 1 := inv_mul_cancel₀ hpos.ne'
  have hs0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hpos.le
  exact ⟨hs0, by nlinarith [mul_nonneg (sub_nonneg.mpr hx) hs0]⟩

/-- Reciprocals of two factors `≥ 3/4` differ by at most `2` times the difference of the
factors. -/
private theorem coeff_inv_sub_abs_le {x y D : ℝ} (hx : 3 / 4 ≤ x) (hy : 3 / 4 ≤ y)
    (hxy : |x - y| ≤ D) : |x⁻¹ - y⁻¹| ≤ 2 * D := by
  obtain ⟨hx0, hx1⟩ := coeff_inv_bounds hx
  obtain ⟨hy0, hy1⟩ := coeff_inv_bounds hy
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hxinv : x⁻¹ * x = 1 := inv_mul_cancel₀ hxpos.ne'
  have hyinv : y⁻¹ * y = 1 := inv_mul_cancel₀ hypos.ne'
  have key : x⁻¹ - y⁻¹ = x⁻¹ * y⁻¹ * (y - x) := by
    linear_combination y⁻¹ * hxinv - x⁻¹ * hyinv
  have hdiff : |y - x| ≤ D := by
    obtain ⟨h1, h2⟩ := abs_le.mp hxy
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod : x⁻¹ * y⁻¹ ≤ 2 := by
    have h := mul_le_mul hx1 hy1 hy0 (by norm_num : (0 : ℝ) ≤ 4 / 3)
    linarith
  rw [key, abs_mul, abs_of_nonneg (mul_nonneg hx0 hy0)]
  exact mul_le_mul hprod hdiff (abs_nonneg (y - x)) (by norm_num)

/-- The difference of squared norms is bounded by the Euclidean norm of the difference,
under `‖g‖, ‖h‖ ≤ 1/4`. Uses `|g|² - |h|² = (g - h) · (g + h)`. -/
private theorem coeff_dot_sub_abs_le {d : ℕ} (g h : Vec d)
    (hg : euclideanNorm g ≤ (1 / 4 : ℝ)) (hh : euclideanNorm h ≤ (1 / 4 : ℝ)) :
    |dot g g - dot h h| ≤ euclideanNorm (g - h) := by
  have hdot : dot g g - dot h h = dot (g - h) (g + h) := by
    unfold dot
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
  have hN : euclideanNorm (g + h) ≤ 1 := (euclideanNorm_add_le g h).trans (by linarith)
  rw [hdot]
  refine (abs_dot_le_euclideanNorm (g - h) (g + h)).trans ?_
  calc euclideanNorm (g - h) * euclideanNorm (g + h)
      ≤ euclideanNorm (g - h) * 1 :=
        mul_le_mul_of_nonneg_left hN (coeff_euclideanNorm_nonneg (g - h))
    _ = euclideanNorm (g - h) := mul_one _

/-- The squared norm of a vector with `‖h‖ ≤ 1/4` is at most one in absolute value. -/
private theorem coeff_dot_self_abs_le {d : ℕ} (h : Vec d) (hh : euclideanNorm h ≤ (1 / 4 : ℝ)) :
    |dot h h| ≤ 1 := by
  have hsq : dot h h = euclideanNorm h ^ 2 := euclideanSq_eq_sq_euclideanNorm h
  rw [hsq, abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_nonneg (coeff_euclideanNorm_nonneg h) (sub_nonneg.mpr hh)]

/-- The scalar-weighted difference `j_g⁻¹ |g|² - j_h⁻¹ |h|²` is bounded by `4 ‖g - h‖` under
`‖g‖, ‖h‖ ≤ 1/4`. Splits as `(|g|² - |h|²) j_g⁻¹ + (j_g⁻¹ - j_h⁻¹) |h|²`. -/
private theorem coeff_inverse_dot_abs_le {d : ℕ} (i : Fin d) (g h : Vec d)
    (hg : euclideanNorm g ≤ (1 / 4 : ℝ)) (hh : euclideanNorm h ≤ (1 / 4 : ℝ)) :
    |(jacobianFactor i g)⁻¹ * dot g g - (jacobianFactor i h)⁻¹ * dot h h| ≤
      4 * euclideanNorm (g - h) := by
  have hD : 0 ≤ euclideanNorm (g - h) := coeff_euclideanNorm_nonneg (g - h)
  obtain ⟨hsg0, hsg1⟩ := coeff_inv_bounds (jacobianFactor_bounds i g hg).1
  have hsgsh : |(jacobianFactor i g)⁻¹ - (jacobianFactor i h)⁻¹| ≤ 2 * euclideanNorm (g - h) :=
    coeff_inv_sub_abs_le (jacobianFactor_bounds i g hg).1 (jacobianFactor_bounds i h hh).1
      (coeff_jf_sub_abs_le i g h)
  have hsg : |(jacobianFactor i g)⁻¹| ≤ 4 / 3 := by
    rw [abs_of_nonneg hsg0]
    exact hsg1
  have hAgAh : |dot g g - dot h h| ≤ euclideanNorm (g - h) := coeff_dot_sub_abs_le g h hg hh
  have hAh : |dot h h| ≤ 1 := coeff_dot_self_abs_le h hh
  have hp := coeff_abs_mul_le hAgAh hsg hD
  have hq := coeff_abs_mul_le hsgsh hAh (by linarith : (0 : ℝ) ≤ 2 * euclideanNorm (g - h))
  have hsplit : (jacobianFactor i g)⁻¹ * dot g g - (jacobianFactor i h)⁻¹ * dot h h =
      (dot g g - dot h h) * (jacobianFactor i g)⁻¹ +
        ((jacobianFactor i g)⁻¹ - (jacobianFactor i h)⁻¹) * dot h h := by
    ring
  rw [hsplit]
  obtain ⟨p1, p2⟩ := abs_le.mp hp
  obtain ⟨q1, q2⟩ := abs_le.mp hq
  rw [abs_le]
  constructor <;> linarith

/-! ### The Lipschitz bound -/

/-- Entrywise Euclidean Lipschitz bound for the sharpness coefficient on small gradients.
Source: `paper/main.tex:1218–1231`, `eq.sharp-coefficients`. For every `d` the constant `L = 8`
is fixed first, and it then works for all `i`, `g`, `h`, `j`, `k`. The norm is the explicit
Euclidean norm `euclideanNorm`. -/
theorem exists_coefficient_euclidean_lipschitz_on_small_gradients :
    (∀ d : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ (i : Fin d) (g h : Vec d),
      euclideanNorm g ≤ (1/4 : ℝ) → euclideanNorm h ≤ (1/4 : ℝ) →
      ∀ j k : Fin d, |coefficient i g j k - coefficient i h j k| ≤ L * euclideanNorm (g-h)) := by
  intro d
  refine ⟨8, by norm_num, fun i g h hg hh j k => ?_⟩
  have hjg := jacobianFactor_bounds i g hg
  have hjh := jacobianFactor_bounds i h hh
  have hgne : jacobianFactor i g ≠ 0 :=
    (show (0 : ℝ) < jacobianFactor i g by linarith [hjg.1]).ne'
  have hhne : jacobianFactor i h ≠ 0 :=
    (show (0 : ℝ) < jacobianFactor i h by linarith [hjh.1]).ne'
  have hD : 0 ≤ euclideanNorm (g - h) := coeff_euclideanNorm_nonneg (g - h)
  have hP1 : |(jacobianFactor i g - jacobianFactor i h) * (1 : Mat d) j k| ≤
      euclideanNorm (g - h) :=
    coeff_abs_mul_le_one (coeff_jf_sub_abs_le i g h) (coeff_one_abs_le j k)
  have hP2 : |(g k - h k) * unitVector i j| ≤ euclideanNorm (g - h) :=
    coeff_abs_mul_le_one (coeff_diff_coord_abs_le k g h) (coeff_unitVector_abs_le i j)
  have hP3 : |(g j - h j) * unitVector i k| ≤ euclideanNorm (g - h) :=
    coeff_abs_mul_le_one (coeff_diff_coord_abs_le j g h) (coeff_unitVector_abs_le i k)
  have hX := coeff_inverse_dot_abs_le i g h hg hh
  have hP4 : |((jacobianFactor i g)⁻¹ * dot g g - (jacobianFactor i h)⁻¹ * dot h h) *
      (unitVector i j * unitVector i k)| ≤ 4 * euclideanNorm (g - h) :=
    coeff_abs_mul_le_one hX (coeff_unitVector_mul_abs_le i j k)
  rw [coefficient_entry_sub i g h j k hgne hhne]
  exact coeff_four_term_abs_le hD hP1 hP2 hP3 hP4

end EinsteinRelation.Sharpness
