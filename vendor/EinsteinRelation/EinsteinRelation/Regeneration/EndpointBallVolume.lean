import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Regeneration.HalfSpaces

/-! # Positive finite volume of the endpoint coupling balls

Source `paper/main.tex:353–374`, endpoint averaging of the actual spatial coupling balls
(`endpointBall`, `endpointAverage` in `Regeneration/Coupling.lean:93–98`).

`endpointBall i R x` is the Euclidean open ball of radius `R` about the translated centre
`x + (9R) • unitVector i`. It is open and contains its centre, so its Lebesgue measure is
positive. Every point of it has each coordinate within `R` of the centre, because
`|x i| ≤ euclideanNorm x` (`coordinate_abs_le_euclideanNorm`). So it lies in the coordinate
sup-norm closed ball of radius `R`, whose Lebesgue measure is finite
(`Real.volume_pi_closedBall`). The sup-norm ball is only a finite comparison set: no norm
instance is introduced, and all balls keep the Euclidean norm `euclideanNorm`.

These facts justify the real denominator `(volume (endpointBall i R x)).toReal` in
`endpointAverage`.
-/

open MeasureTheory

namespace EinsteinRelation.Regeneration

/-- The Euclidean norm is continuous on the coordinate space. -/
private theorem continuous_euclideanNorm_ballVolume {d : ℕ} :
    Continuous (fun v : Vec d => euclideanNorm v) := by
  have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) := by
    apply continuous_finset_sum
    intro j _
    exact (continuous_apply j).mul (continuous_apply j)
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp hsum

/-- The endpoint ball is open, being a sublevel set of a continuous function. -/
private theorem isOpen_endpointBall {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d) :
    IsOpen (endpointBall i R x) := by
  have hc : Continuous (fun y : Vec d => y - (x + (9 * R) • unitVector i)) :=
    continuous_id.sub continuous_const
  have hcont : Continuous (fun y : Vec d => euclideanNorm (y - (x + (9 * R) • unitVector i))) :=
    continuous_euclideanNorm_ballVolume.comp hc
  unfold endpointBall
  exact isOpen_lt hcont continuous_const

/-- The centre of the endpoint ball lies in it, since the Euclidean norm of zero is `0 < R`. -/
private theorem endpointBall_nonempty {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R) (x : Vec d) :
    (endpointBall i R x).Nonempty := by
  refine ⟨x + (9 * R) • unitVector i, ?_⟩
  have hzero : euclideanNorm (0 : Vec d) = 0 := by
    simp [euclideanNorm, euclideanSq, dot]
  show euclideanNorm ((x + (9 * R) • unitVector i) - (x + (9 * R) • unitVector i)) < R
  rw [sub_self, hzero]
  exact hR

/-- The endpoint ball lies in the coordinate sup-norm closed ball of radius `R` about its
centre, since each coordinate is bounded by the Euclidean norm. -/
private theorem endpointBall_subset_closedBall {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R)
    (x : Vec d) :
    endpointBall i R x ⊆ Metric.closedBall (x + (9 * R) • unitVector i) R := by
  intro y hy
  have hy' : euclideanNorm (y - (x + (9 * R) • unitVector i)) < R := hy
  rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
  intro j
  rw [Real.dist_eq]
  have hj := coordinate_abs_le_euclideanNorm (y - (x + (9 * R) • unitVector i)) j
  rw [Pi.sub_apply] at hj
  exact hj.trans hy'.le

/-- Source `paper/main.tex:353–374`: the endpoint coupling ball has positive Lebesgue
volume, so the denominator of `endpointAverage` is not zero. -/
theorem endpointBall_volume_pos {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R) (x : Vec d) :
    0 < volume (endpointBall i R x) :=
  (isOpen_endpointBall i R x).measure_pos volume (endpointBall_nonempty i R hR x)

/-- Source `paper/main.tex:353–374`: the endpoint coupling ball has finite Lebesgue volume,
so `(volume (endpointBall i R x)).toReal` is a genuine real number in `endpointAverage`. -/
theorem endpointBall_volume_ne_top {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R) (x : Vec d) :
    volume (endpointBall i R x) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (endpointBall_subset_closedBall i R hR x))
  rw [Real.volume_pi_closedBall _ hR.le]
  exact ENNReal.ofReal_ne_top

/-- The real denominator `(volume (endpointBall i R x)).toReal` of `endpointAverage` is
strictly positive. -/
private theorem endpointBall_volume_toReal_pos {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R)
    (x : Vec d) :
    0 < (volume (endpointBall i R x)).toReal :=
  ENNReal.toReal_pos (endpointBall_volume_pos i R hR x).ne'
    (endpointBall_volume_ne_top i R hR x)

end EinsteinRelation.Regeneration
