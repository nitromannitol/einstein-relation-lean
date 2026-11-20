import EinsteinFull.Homogenization.MultiscalePoincareTruncation

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

end EinsteinFull.Homogenization
