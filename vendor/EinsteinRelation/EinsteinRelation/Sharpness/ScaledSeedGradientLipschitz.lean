import EinsteinRelation.Sharpness.ScaledSeedDerivatives
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.MeanValue

/-! # Euclidean Lipschitz bound for the gradient of the scaled canonical seed

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218, and the coefficient
regularity in lines 1218–1231. The field `ψ = ε * seedField d W` is the one of line 1218. The
coefficients of lines 1218–1231 are built from `∇ψ`, so their Lipschitz property rests on the
Lipschitz property of `∇ψ` proved here.

For each fixed `ε` and dimension `d`, one constant `L = d² M ≥ 0` is chosen first, where `M` is the
common deterministic bound on the second coordinate jets from
`exists_uniform_scaled_seedField_third_jet_bound`. It then works for every actual sample `W` and
every pair of points `x`, `y`. No probability law, smoothness premise, or gradient bound is assumed.

The norm is the explicit Euclidean norm `euclideanNorm`. The proof never uses the sup-norm on
`Vec d`: each coordinate difference of the gradient is bounded by the `ℓ¹` size of `x - y` times
`M`, and the Euclidean norm is at most the `ℓ¹` norm of the coordinates.

The same argument applied to the second coordinate jets `∂_i ∂_j ψ` gives
`exists_uniform_scaled_seedField_hessian_euclidean_lipschitz`, with constant `d * M`: the
derivatives of `∂_i ∂_j ψ` are the actual third jets, already bounded by the same `M`.
-/

namespace EinsteinRelation.Sharpness

/-- Each coordinate of a vector is bounded by its Euclidean norm. -/
private theorem scaledGrad_coord_abs_le {d : ℕ} (i : Fin d) (v : Vec d) :
    |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [pow_two]
  exact Finset.single_le_sum (f := fun j => v j * v j)
    (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)

/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
private theorem scaledGrad_euclideanNorm_le_sum_abs {d : ℕ} (v : Vec d) :
    euclideanNorm v ≤ ∑ i, |v i| := by
  have hs : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg (v i)
  have hle : ∀ i, |v i| ≤ ∑ j, |v j| := fun i =>
    Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
  have hsq1 : ∑ i, v i * v i ≤ ∑ i, |v i| * ∑ j, |v j| := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← abs_mul_abs_self (v i)]
    exact mul_le_mul_of_nonneg_left (hle i) (abs_nonneg _)
  have hsq2 : ∑ i, |v i| * ∑ j, |v j| = (∑ i, |v i|) ^ 2 := by
    rw [← Finset.sum_mul, sq]
  have hsq : euclideanSq v ≤ (∑ i, |v i|) ^ 2 := by
    unfold euclideanSq dot
    exact hsq1.trans_eq hsq2
  unfold euclideanNorm
  rw [← Real.sqrt_sq hs]
  exact Real.sqrt_le_sqrt hsq

/-- The directional derivative of a function along `u` is the coordinate sum `∑ j, u j ∂_j`. -/
private theorem scaledGrad_fderiv_apply_eq_sum {d : ℕ} (h : Vec d → ℝ) (z u : Vec d) :
    fderiv ℝ h z u = ∑ j, u j * coordinateDerivative j h z := by
  conv_lhs => rw [pi_eq_sum_univ' u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- Along the line `s ↦ y + s • u`, the coordinate derivative `∂_i f` of a smooth `f` has the
derivative `∑ j, u j * ∂_j ∂_i f` at every parameter. -/
private theorem scaledGrad_coordinate_hasDerivAt {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) (y u : Vec d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordinateDerivative i f (y + s • u))
      (∑ j, u j * coordinateDerivative j (coordinateDerivative i f) (y + t • u)) t := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) :=
    contDiff_iteratedCoordinateDerivative f hf [i]
  have hd : DifferentiableAt ℝ (coordinateDerivative i f) (y + t • u) :=
    (hc.differentiable (by simp)) _
  have hline : HasDerivAt (fun s : ℝ => y + s • u) u t := by
    simpa using ((hasDerivAt_id' (x := t)).smul_const u).const_add y
  have hcomp := HasFDerivAt.comp_hasDerivAt (x := t) hd.hasFDerivAt hline
  rw [scaledGrad_fderiv_apply_eq_sum] at hcomp
  exact hcomp

/-- Coordinate Lipschitz bound with the common second-jet constant `M`. The `i`-th coordinate of the
gradient changes by at most `(∑ j, |(x - y) j|) * M` between `y` and `x`, by the mean value theorem
on the segment `[y, x]`. -/
private theorem scaledGrad_coordinate_sub_abs_le {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) (M : ℝ)
    (hH : ∀ j : Fin d, ∀ z : Vec d, |coordinateDerivative j (coordinateDerivative i f) z| ≤ M)
    (x y : Vec d) :
    |coordinateDerivative i f x - coordinateDerivative i f y| ≤ (∑ j, |(x - y) j|) * M := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => coordinateDerivative i f (y + s • (x - y)))
      (∑ j, (x - y) j * coordinateDerivative j (coordinateDerivative i f) (y + t • (x - y))) t :=
    fun t => scaledGrad_coordinate_hasDerivAt f hf i y (x - y) t
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖∑ j, (x - y) j * coordinateDerivative j (coordinateDerivative i f) (y + t • (x - y))‖ ≤
        (∑ j, |(x - y) j|) * M := by
    intro t _
    rw [Real.norm_eq_abs, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hH j _) (abs_nonneg _)
  have hmvt : ‖coordinateDerivative i f (y + (1 : ℝ) • (x - y)) -
      coordinateDerivative i f (y + (0 : ℝ) • (x - y))‖ ≤ (∑ j, |(x - y) j|) * M :=
    norm_image_sub_le_of_norm_deriv_le_segment_01' (fun t _ => (hderiv t).hasDerivWithinAt) hbound
  have h1 : y + (1 : ℝ) • (x - y) = x := by
    rw [one_smul]
    abel
  have h0 : y + (0 : ℝ) • (x - y) = y := by
    rw [zero_smul, add_zero]
  rw [h1, h0, Real.norm_eq_abs] at hmvt
  exact hmvt

/-- Euclidean Lipschitz bound for the gradient of a smooth field whose second coordinate jets are
bounded by `M`. The constant `d² * M` depends only on the dimension and on `M`. -/
private theorem scaledGrad_gradient_euclidean_lipschitz {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (M : ℝ) (hM : 0 ≤ M)
    (hH : ∀ i j : Fin d, ∀ z : Vec d, |coordinateDerivative i (coordinateDerivative j f) z| ≤ M)
    (x y : Vec d) :
    euclideanNorm (gradient f x - gradient f y) ≤ (d : ℝ) ^ 2 * M * euclideanNorm (x - y) := by
  have hsum : ∑ j, |(x - y) j| ≤ (d : ℝ) * euclideanNorm (x - y) := by
    calc ∑ j, |(x - y) j| ≤ ∑ _j : Fin d, euclideanNorm (x - y) :=
          Finset.sum_le_sum fun j _ => scaledGrad_coord_abs_le j (x - y)
      _ = (d : ℝ) * euclideanNorm (x - y) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcoord : ∀ i : Fin d,
      |(gradient f x - gradient f y) i| ≤ (d : ℝ) * euclideanNorm (x - y) * M := by
    intro i
    have h1 := scaledGrad_coordinate_sub_abs_le f hf i M (fun j z => hH j i z) x y
    have h2 : (∑ j, |(x - y) j|) * M ≤ (d : ℝ) * euclideanNorm (x - y) * M :=
      mul_le_mul_of_nonneg_right hsum hM
    rw [Pi.sub_apply]
    exact h1.trans h2
  calc euclideanNorm (gradient f x - gradient f y)
      ≤ ∑ i, |(gradient f x - gradient f y) i| := scaledGrad_euclideanNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, (d : ℝ) * euclideanNorm (x - y) * M :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) ^ 2 * M * euclideanNorm (x - y) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218, and the coefficient
regularity in lines 1218–1231. For every dimension `d` and every scale `ε`, there is one constant
`L ≥ 0`, chosen before the actual sample `W` and the points `x`, `y`, such that the Euclidean
gradient of `ε * seedField d W` is `L`-Lipschitz for the Euclidean norm. -/
theorem exists_uniform_scaled_seedField_gradient_euclidean_lipschitz :
    ∀ (d : ℕ) (ε : ℝ), ∃ L : ℝ, 0 ≤ L ∧
      ∀ (W : NoiseSample d) (x y : Vec d),
        euclideanNorm (gradient (fun z => ε * seedField d W z) x -
          gradient (fun z => ε * seedField d W z) y) ≤ L * euclideanNorm (x - y) := by
  intro d ε
  obtain ⟨M, hM, hb⟩ := exists_uniform_scaled_seedField_third_jet_bound d ε
  refine ⟨(d : ℝ) ^ 2 * M, mul_nonneg (sq_nonneg _) hM, fun W x y => ?_⟩
  exact scaledGrad_gradient_euclidean_lipschitz (fun z => ε * seedField d W z)
    (contDiff_const.mul (contDiff_seedField d W)) M hM (fun i j z => (hb W z).2.2.1 i j) x y

/-- The `ℓ¹` size of a vector is at most `d` times its Euclidean norm, since each coordinate is
bounded by the Euclidean norm. -/
private theorem scaledGrad_sum_abs_le_dim_mul {d : ℕ} (v : Vec d) :
    ∑ j, |v j| ≤ (d : ℝ) * euclideanNorm v := by
  calc ∑ j, |v j| ≤ ∑ _j : Fin d, euclideanNorm v :=
        Finset.sum_le_sum fun j _ => scaledGrad_coord_abs_le j v
    _ = (d : ℝ) * euclideanNorm v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218, and the coefficient
regularity in lines 1218–1231. For every dimension `d` and every scale `ε`, there is one constant
`L ≥ 0`, chosen before the actual sample `W`, the coordinates `i`, `j`, and the points `x`, `y`, such
that each actual second coordinate jet `∂_i ∂_j (ε * seedField d W)` is `L`-Lipschitz for the
Euclidean norm. -/
theorem exists_uniform_scaled_seedField_hessian_euclidean_lipschitz :
    ∀ (d : ℕ) (ε : ℝ), ∃ L : ℝ, 0 ≤ L ∧
      ∀ (W : NoiseSample d) (i j : Fin d) (x y : Vec d),
        |coordinateDerivative i (coordinateDerivative j (fun z => ε * seedField d W z)) x -
          coordinateDerivative i (coordinateDerivative j (fun z => ε * seedField d W z)) y| ≤
          L * euclideanNorm (x - y) := by
  intro d ε
  obtain ⟨M, hM, hb⟩ := exists_uniform_scaled_seedField_third_jet_bound d ε
  refine ⟨(d : ℝ) * M, mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hM, fun W i j x y => ?_⟩
  -- `f = ∂_j ψ` is smooth, and `∂_k ∂_i f = ∂_k ∂_i ∂_j ψ` is a third jet bounded by `M`.
  have hf : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j (fun z => ε * seedField d W z)) :=
    contDiff_iteratedCoordinateDerivative (fun z => ε * seedField d W z)
      (contDiff_const.mul (contDiff_seedField d W)) [j]
  have h1 := scaledGrad_coordinate_sub_abs_le
    (coordinateDerivative j (fun z => ε * seedField d W z)) hf i M
    (fun k z => (hb W z).2.2.2 k i j) x y
  have h2 : (∑ k, |(x - y) k|) * M ≤ (d : ℝ) * M * euclideanNorm (x - y) := by
    calc (∑ k, |(x - y) k|) * M ≤ ((d : ℝ) * euclideanNorm (x - y)) * M :=
          mul_le_mul_of_nonneg_right (scaledGrad_sum_abs_le_dim_mul (x - y)) hM
      _ = (d : ℝ) * M * euclideanNorm (x - y) := by ring
  exact h1.trans h2

end EinsteinRelation.Sharpness
