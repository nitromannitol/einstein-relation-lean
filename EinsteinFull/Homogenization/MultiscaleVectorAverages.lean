import EinsteinFull.Homogenization.MultiscalePoincareTruncation
import Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12LocalPoincare

/-!
# Vector-valued block averages

Coordinate block averages are controlled by the Euclidean vector average in
the multiscale Poincaré inequality of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Corollary 1.14.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- Every coordinate depth term is bounded by the Euclidean root mean square of
vector block averages; all coordinate averages are integrable on descendants. -/
theorem integrable_and_originCubeBesovDepth_le_vector
    {d : ℕ} (n j : ℕ) (hj : j ≤ n) (G : Vec d → Vec d)
    (hG : ∀ i, MemLp (fun x => G x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    (∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) j, ∀ i,
      Integrable (fun x => G x i) (normalizedCubeMeasure R)) ∧
    (∀ i, cubeBesovCircDepthSeminorm (originCube d (n : ℤ)) 1 (2 : ℝ≥0∞)
        (fun x => G x i) j ≤
      (3 : ℝ) ^ (n - j) * Real.sqrt
        (descendantsAverage (originCube d (n : ℤ)) j
          (fun R => vecNormSq (fun l => cubeAverage R (fun x => G x l))))) := by
  refine ⟨?_, ?_⟩
  · intro R hR i
    exact (memLp_on_descendant_of_memLp hR (hG i)).integrable (by norm_num)
  · intro i
    rw [originCubeBesovCircDepthSeminorm_eq n j hj]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_sqrt
    apply descendantsAverage_le_descendantsAverage
    intro R _
    exact sq_apply_le_vecNormSq (fun l => cubeAverage R (fun x => G x l)) i

/-- The Euclidean length of an `H¹` gradient is in normalized `L²`, and its
norm controls every coordinate `L²` norm. -/
theorem memLp_and_cubeLpNorm_grad_coord_le_euclidean
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    MemLp (fun x => euclideanNorm (u.grad x)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
    ∀ i, cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.grad x i) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) := by
  let v : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞) :=
    { toFun := u.toFun
      grad := u.grad
      memLp := u.memL2
      gradMemLp := u.gradMemL2
      hasWeakGradient := u.hasWeakGradient }
  let U : BoundedMeasurableDomain d :=
    (isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
      (Book.Ch02.openCubeSet_nonempty Q)
  have hm : MemLp (fun x => euclideanNorm (u.grad x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa only [U, v, openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using v.gradEuclideanMemLp U (2 : ℝ≥0∞)
  refine ⟨hm, ?_⟩
  intro i
  unfold cubeLpNorm
  apply ENNReal.toReal_mono hm.eLpNorm_ne_top
  apply eLpNorm_mono_ae (u.grad_coord_memL2_normalizedCubeMeasure i).aestronglyMeasurable
  filter_upwards [] with x
  have h := Real.sqrt_le_sqrt (sq_apply_le_vecNormSq (u.grad x) i)
  simpa only [euclideanNorm, Real.sqrt_sq_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using h

end EinsteinFull.Homogenization
