import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Geometry of shifted local-corrector balls

Source: `paper/main.tex:892–898,926–938`.
-/

open EinsteinRelation.TimeChange

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:931–938`. Every coefficient observed by a
contributing center lies in the radius-33R ball at the evaluation point. -/
theorem local_center_ball_subset {d : ℕ} {R : ℝ} {x y : Vec d}
    (hxy : euclideanNorm (x - y) ≤ R) :
    {z : Vec d | euclideanNorm (z - y) < 32 * R} ⊆
      {z : Vec d | euclideanNorm (z - x) < 33 * R} := by
  intro z hz
  simp at hz ⊢
  have hneg : euclideanNorm (-(x - y)) = euclideanNorm (x - y) := by
    calc
      euclideanNorm (-(x - y)) = euclideanNorm ((-1 : ℝ) • (x - y)) := by simp
      _ = |(-1 : ℝ)| * euclideanNorm (x - y) := euclideanNorm_smul (-1) (x - y)
      _ = 1 * euclideanNorm (x - y) := by norm_num
      _ = euclideanNorm (x - y) := by simp
  calc
    euclideanNorm (z - x) = euclideanNorm ((z - y) + (y - x)) := by
      simp [sub_add_sub_cancel]
    _ ≤ euclideanNorm (z - y) + euclideanNorm (y - x) := euclideanNorm_add_le (z - y) (y - x)
    _ = euclideanNorm (z - y) + euclideanNorm (-(x - y)) := by rw [← neg_sub x y]
    _ = euclideanNorm (z - y) + euclideanNorm (x - y) := by rw [hneg]
    _ < 32 * R + R := by linarith
    _ = 33 * R := by ring

/-- Source: `paper/main.tex:951–960`. A center at distance at most R
observes the common radius-16R ball. -/
theorem common_ball_subset_center_ball {d : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {y : Vec d} (hy : euclideanNorm y ≤ R) :
    {z : Vec d | euclideanNorm z < 16 * R} ⊆
      {z : Vec d | euclideanNorm (z - y) < 32 * R} := by
  intro z hz
  simp at hz ⊢
  have hneg : euclideanNorm (-(y : Vec d)) = euclideanNorm y := by
    calc
      euclideanNorm (-(y : Vec d)) = euclideanNorm ((-1 : ℝ) • y) := by simp
      _ = |(-1 : ℝ)| * euclideanNorm y := euclideanNorm_smul (-1) y
      _ = 1 * euclideanNorm y := by norm_num
      _ = euclideanNorm y := by simp
  calc
    euclideanNorm (z - y) = euclideanNorm ((z : Vec d) + (-y)) := by rw [sub_eq_add_neg]
    _ ≤ euclideanNorm z + euclideanNorm (-y) := euclideanNorm_add_le z (-y)
    _ = euclideanNorm z + euclideanNorm y := by rw [hneg]
    _ < 16 * R + R := by linarith
    _ ≤ 32 * R := by
      nlinarith

end EinsteinRelation.Correctors
