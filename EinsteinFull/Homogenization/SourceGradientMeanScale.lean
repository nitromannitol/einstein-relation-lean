import EinsteinFull.Homogenization.SourceGradientDescendantMean
import EinsteinFull.Homogenization.SourceResponseDefectSum

/-!
# Mean gradient across scales

The response defects control changes in the mean optimizer gradient across
scales, following Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, equation (2.44).
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Each coordinate of the mean gradient changes across scales by at most the
square root of the sum of the intervening response defects times `4d`. -/
theorem sq_integral_sourceGradient_sub_le_sum_tau
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (m n k : ℕ) (hmn : m ≤ n) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) (i : Fin d) :
    (∀ r : ℕ, Integrable (fun a => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)) p q).toSolution i) P) ∧
    ((∫ a, Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution i ∂P) -
     (∫ a, Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (m : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (m : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (m : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (m : ℤ))) k hk)) p q).toSolution i ∂P)) ^ 2 ≤
    (4 * d) * ∑ j ∈ Finset.Ico m n, sourceResponseTau P j k hk := by
  classical
  refine ⟨fun r => (memLp_sourceResponseAverageGradient_cube P
    (originCube d (r : ℤ)) k hk p q i 2).integrable (by norm_num), ?_⟩
  let Q := originCube d (n : ℤ)
  let j := n - m
  have hscale : Q.scale = (m : ℤ) + j := by
    dsimp [Q, j]
    simp only [originCube, Nat.cast_sub hmn]
    ring
  let X := fun a : Coefficient d K => Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
    (regularCoefficient a).toFun i
  let Y := fun a : Coefficient d K => descendantsAverage Q j (fun R =>
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
      (regularCoefficient a).toFun i)
  have hX : Integrable X P := by
    simpa only [X, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using
      (memLp_sourceResponseAverageGradient_cube P Q k hk p q i 2).integrable (by norm_num)
  have hY : Integrable Y P := by
    have hs := memLp_finsetSum' (descendantsAtDepth Q j) (fun R _ =>
      memLp_sourceResponseAverageGradient_cube P R k hk p q i 2)
    have hc := (hs.const_mul (((descendantsAtDepth Q j).card : ℝ)⁻¹)).integrable (by norm_num)
    simpa only [Y, descendantsAverage, Finset.sum_apply,
      sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using hc
  have h := sq_integral_sourceGradientMismatch_le hK P hstat Q j m hscale k hk p q i
  have h := h.2.2.2
  change (∫ a, (X a - Y a) ∂P) ^ 2 ≤ _ at h
  rw [integral_sub hX hY, integral_descendantsAverage_sourceGradient_eq_origin P hstat Q j m
    hscale k hk p q i] at h
  simp only [X, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] at h
  have ht := expected_sourceResponseJ_sub_le_sum_tau hK P m n k hmn hk p q hp hq
  have hc : (0 : ℝ) ≤ 4 * d := by positivity
  calc
    _ ≤ (4 * d) * ((∫ a, Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (originCube d (m : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (m : ℤ))) k hk) p q ∂P) -
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P)) := by
          simpa only [Q] using h
    _ ≤ _ := mul_le_mul_of_nonneg_left ht.2 hc

end EinsteinFull.Homogenization
