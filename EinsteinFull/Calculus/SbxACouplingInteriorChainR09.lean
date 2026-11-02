import EinsteinFull.Calculus.SbxBCappedTubeChainR02
import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinRelation.Regeneration.Coupling

/-! Euclidean geometry of the full coupling endpoint ball. -/

open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP

namespace EinsteinFull.Calculus

private theorem a_unit_euclidean_norm {d : ℕ} (i : Fin d) :
    euclideanNorm (unitVector i) = 1 := by
  change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

/-- The start and every point of the full endpoint ball have margin `R/2`
inside the actual coupling ball. -/
theorem a_coupling_endpoint_margins {d : ℕ} (i : Fin d) (R : ℝ) (x y : Vec d)
    (hR : 0 < R) (hy : y ∈ endpointBall i R x) :
    euclideanNorm (x - (x + (5 * R) • unitVector i)) + R / 2 < 6 * R ∧
    euclideanNorm (y - (x + (5 * R) • unitVector i)) + R / 2 < 6 * R := by
  change euclideanNorm (y - (x + (9 * R) • unitVector i)) < R at hy
  have hs : x - (x + (5 * R) • unitVector i) = (-5 * R) • unitVector i := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hn : euclideanNorm (x - (x + (5 * R) • unitVector i)) = 5 * R := by
    rw [hs, TimeChange.euclideanNorm_smul, a_unit_euclidean_norm, mul_one,
      abs_of_nonpos (by nlinarith : -5 * R ≤ 0)]
    ring
  have hv : y - (x + (5 * R) • unitVector i) =
      (y - (x + (9 * R) • unitVector i)) + (4 * R) • unitVector i := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ht := TimeChange.euclideanNorm_add_le
    (y - (x + (9 * R) • unitVector i)) ((4 * R) • unitVector i)
  rw [← hv, TimeChange.euclideanNorm_smul, a_unit_euclidean_norm, mul_one,
    abs_of_nonneg (by positivity : 0 ≤ 4 * R)] at ht
  constructor <;> linarith

/-- The whole endpoint ball is at Euclidean distance less than `10R` from
its corresponding start. -/
theorem a_coupling_endpoint_distance {d : ℕ} (i : Fin d) (R : ℝ) (x y : Vec d)
    (hR : 0 < R) (hy : y ∈ endpointBall i R x) :
    euclideanNorm (y - x) < 10 * R := by
  change euclideanNorm (y - (x + (9 * R) • unitVector i)) < R at hy
  have hv : y - x =
      (y - (x + (9 * R) • unitVector i)) + (9 * R) • unitVector i := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ht := TimeChange.euclideanNorm_add_le
    (y - (x + (9 * R) • unitVector i)) ((9 * R) • unitVector i)
  rw [← hv, TimeChange.euclideanNorm_smul, a_unit_euclidean_norm, mul_one,
    abs_of_nonneg (by positivity : 0 ≤ 9 * R)] at ht
  linarith

/-- A ball of radius `R/2` around any point of the segment from the start to
an endpoint remains in the actual coupling region. -/
theorem a_coupling_segment_margin {d : ℕ} (i : Fin d) (R : ℝ) (x y : Vec d)
    (hR : 0 < R) (hy : y ∈ endpointBall i R x) (u : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    sourceBall ((1-u) • x + u • y) (R/2) ⊆ couplingRegion i R x := by
  obtain ⟨hx, hy'⟩ := a_coupling_endpoint_margins i R x y hR hy
  have hm := b_tube_segment_inside_margin (x + (5 * R) • unitVector i) x y
    (6 * R) (R/2) u hu0 hu1 hx hy'
  intro z hz
  change euclideanNorm (z - ((1-u) • x + u • y)) < R/2 at hz
  change euclideanNorm (z - (x + (5 * R) • unitVector i)) < 6 * R
  have ht := TimeChange.euclideanNorm_add_le (z - ((1-u) • x + u • y))
    (((1-u) • x + u • y) - (x + (5 * R) • unitVector i))
  have hv : z - ((1-u) • x + u • y) +
      (((1-u) • x + u • y) - (x + (5 * R) • unitVector i)) =
        z - (x + (5 * R) • unitVector i) := by abel
  rw [hv] at ht
  linarith

/-- Every equispaced center has the same ball margin, including both endpoints. -/
theorem a_coupling_equispaced_margin {d : ℕ} (i : Fin d) (R : ℝ) (x y : Vec d)
    (hR : 0 < R) (hy : y ∈ endpointBall i R x) (n k : ℕ)
    (hn : 0 < n) (hk : k ≤ n) :
    sourceBall (b_tube_segment_center x y n k) (R/2) ⊆ couplingRegion i R x := by
  obtain ⟨hx, hy'⟩ := a_coupling_endpoint_margins i R x y hR hy
  intro z hz
  change euclideanNorm (z - b_tube_segment_center x y n k) < R/2 at hz
  change euclideanNorm (z - (x + (5 * R) • unitVector i)) < 6 * R
  exact b_equispaced_segment_margin_ball _ x y z n k (6*R) (R/2) hn hk hx hy' hz

/-- For at least eighty subdivisions, points in consecutive `R/16` balls
lie together in the inner half of the `R/2` ball at the first center. -/
theorem a_coupling_consecutive_inner_ball {d : ℕ} (i : Fin d) (R : ℝ)
    (x y : Vec d) (hR : 0 < R) (hy : y ∈ endpointBall i R x)
    (n k : ℕ) (hn : 80 ≤ n) (z w : Vec d)
    (hz : z ∈ sourceBall (b_tube_segment_center x y n k) (R/16))
    (hw : w ∈ sourceBall (b_tube_segment_center x y n (k+1)) (R/16)) :
    z ∈ sourceBall (b_tube_segment_center x y n k) (R/4) ∧
    w ∈ sourceBall (b_tube_segment_center x y n k) (R/4) := by
  have hn' : (80 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hxy := a_coupling_endpoint_distance i R x y hR hy
  have hgap : ((k+1 : ℕ) : ℝ) / (n : ℝ) - (k : ℝ) / (n : ℝ) =
      (n : ℝ)⁻¹ := by
    push_cast
    ring
  have hstep : euclideanNorm (b_tube_segment_center x y n (k+1) -
      b_tube_segment_center x y n k) ≤ R/8 := by
    dsimp [b_tube_segment_center]
    rw [b_tube_segment_distance, hgap, abs_of_nonneg (inv_nonneg.mpr hn0.le)]
    have hm := mul_le_mul_of_nonneg_left hxy.le (inv_nonneg.mpr hn0.le)
    have hbound : (n : ℝ)⁻¹ * (10 * R) ≤ R/8 := by
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ hn0).2
      nlinarith
    exact le_trans hm hbound
  change euclideanNorm (z - b_tube_segment_center x y n k) < R/16 at hz
  change euclideanNorm (w - b_tube_segment_center x y n (k+1)) < R/16 at hw
  constructor
  · change euclideanNorm (z - b_tube_segment_center x y n k) < R/4
    linarith
  · change euclideanNorm (w - b_tube_segment_center x y n k) < R/4
    have ht := TimeChange.euclideanNorm_add_le
      (w - b_tube_segment_center x y n (k+1))
      (b_tube_segment_center x y n (k+1) - b_tube_segment_center x y n k)
    have hv : w - b_tube_segment_center x y n (k+1) +
        (b_tube_segment_center x y n (k+1) - b_tube_segment_center x y n k) =
          w - b_tube_segment_center x y n k := by abel
    rw [hv] at ht
    linarith

end EinsteinFull.Calculus

