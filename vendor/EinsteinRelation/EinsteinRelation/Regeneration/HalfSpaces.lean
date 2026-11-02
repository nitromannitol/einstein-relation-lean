import EinsteinRelation.Environment.Basic

open scoped BigOperators
namespace EinsteinRelation.Regeneration

/-!
Scalar half-space prerequisites for the regeneration step, from `paper/main.tex`
lines 331--340 (`regen.future`, the half-space `R₊ = {e₁·x ≥ -2R}`) and lines
377--403 (the corrected past and future half-spaces, separated by `2R`).

Every declaration here is a coordinate fact about the explicit Euclidean norm
`euclideanNorm`. None of them is the paper's regeneration lemma, the factorization
at `τ₁`, the finite-range argument, or any other probabilistic claim of the paper.
-/

/-- Scalar prerequisite: each coordinate of a vector is bounded by its Euclidean
norm. -/
theorem coordinate_abs_le_euclideanNorm {d : ℕ} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  have hsq : x i * x i ≤ ∑ j, x j * x j :=
    Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact hsq

/-- Scalar prerequisite for the corrected half-spaces (`paper/main.tex:377--403`):
if `x i ≤ y - 4R` and `y - 2R ≤ z i`, the coordinate gap is at least `2R`, so the
Euclidean distance between `x` and `z` is at least `2R`. -/
theorem corrected_halfSpace_gap {d : ℕ} (i : Fin d) (x z : Vec d) (y R : ℝ) (hx : x i ≤ y - 4 * R) (hz : y - 2 * R ≤ z i) :
    2 * R ≤ euclideanNorm (x - z) := by
  have hxz : (x - z) i = x i - z i := Pi.sub_apply x z i
  have hcoord : -((x - z) i) ≤ |(x - z) i| := neg_le_abs _
  have hnorm := coordinate_abs_le_euclideanNorm (x - z) i
  linarith

/-- Scalar prerequisite for `regen.future` (`paper/main.tex:331--340`): if `z i ≥ -R`
and `x` is within Euclidean distance `R` of `z`, then `x i ≥ -2R`, i.e. `x` lies in
the coordinate half-space `{x i ≥ -2R}`. -/
theorem future_ball_in_halfSpace {d : ℕ} (i : Fin d) (x z : Vec d) (R : ℝ) (hz : -R ≤ z i) (hx : euclideanNorm (x - z) < R) :
    -2 * R ≤ x i := by
  have hxz : (x - z) i = x i - z i := Pi.sub_apply x z i
  have hnorm := coordinate_abs_le_euclideanNorm (x - z) i
  have habs : |(x - z) i| < R := lt_of_le_of_lt hnorm hx
  have hlow : -R < (x - z) i := (abs_lt.mp habs).1
  linarith

/-- Scalar prerequisite for the coupling ball (`paper/main.tex:377--403`): if `z i ≥ -R`
and `x` is within Euclidean distance `6R` of `z + 5R e_i`, then `x i ≥ -2R`. -/
theorem coupling_ball_in_halfSpace {d : ℕ} (i : Fin d) (x z : Vec d) (R : ℝ) (hz : -R ≤ z i) (hx : euclideanNorm (x - (z + (5 * R) • unitVector i)) < 6 * R) :
    -2 * R ≤ x i := by
  have hshift : (x - (z + (5 * R) • unitVector i)) i = x i - (z i + 5 * R) := by
    simp [unitVector]
  have hnorm := coordinate_abs_le_euclideanNorm (x - (z + (5 * R) • unitVector i)) i
  have habs : |(x - (z + (5 * R) • unitVector i)) i| < 6 * R := lt_of_le_of_lt hnorm hx
  have hlow : -(6 * R) < (x - (z + (5 * R) • unitVector i)) i := (abs_lt.mp habs).1
  linarith

end EinsteinRelation.Regeneration
