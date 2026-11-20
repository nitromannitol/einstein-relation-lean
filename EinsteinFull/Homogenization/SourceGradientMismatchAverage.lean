import EinsteinFull.Homogenization.SourceGradientPartition
import EinsteinFull.Homogenization.SourceResponseGradientExpectation
import Mathlib.Algebra.Order.Chebyshev

/-!
# Optimizer gradient mismatch after averaging

The mean squared optimizer-gradient mismatch in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Lemma 2.13,
controls the square of the difference between parent and child averages.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Squaring a descendant average is bounded by averaging the squares. -/
theorem sq_descendantsAverage_le {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (f : TriadicCube d → ℝ) :
    (descendantsAverage Q j f) ^ 2 ≤ descendantsAverage Q j (fun R => (f R) ^ 2) := by
  classical
  have h := sum_div_card_sq_le_sum_sq_div_card (α := ℝ)
    (s := descendantsAtDepth Q j) (f := f)
  simpa [descendantsAverage, div_eq_mul_inv, mul_comm] using h

/-- The squared difference of parent and descendant-averaged gradients is
bounded by the mean squared gradient mismatch. -/
theorem sq_sourceGradientAverage_sub_descendantsAverage_le_meanMismatch
    {d : ℕ} [NeZero d] {K : ℝ} (a : Coefficient d K) (Q : TriadicCube d)
    (j : ℕ) (p q : Vec d) (i : Fin d) :
    (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
        (regularCoefficient a).toFun i -
      descendantsAverage Q j (fun R =>
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun i)) ^ 2 ≤
    descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun -
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun)) := by
  classical
  let f : TriadicCube d → ℝ := fun R =>
    (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
      (regularCoefficient a).toFun -
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
      (regularCoefficient a).toFun) i
  have heq : Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
        (regularCoefficient a).toFun i -
      descendantsAverage Q j (fun R =>
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun i) = descendantsAverage Q j f := by
    rw [sourceResponseGradientAverage_eq_descendantsAverage a Q j p q i]
    simp [descendantsAverage, f, Finset.sum_sub_distrib, mul_sub]
  rw [heq]
  calc
    _ ≤ descendantsAverage Q j (fun R => (f R) ^ 2) := sq_descendantsAverage_le Q j f
    _ ≤ descendantsAverage Q j (fun R =>
        vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
            (regularCoefficient a).toFun -
          Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
            (regularCoefficient a).toFun)) := by
      apply descendantsAverage_le_descendantsAverage
      intro R _
      unfold f vecNormSq vecDot
      rw [sq]
      exact Finset.single_le_sum (fun l _ => mul_self_nonneg _) (Finset.mem_univ i)

/-- The squared difference between the parent optimizer gradient and the
average of descendant optimizer gradients is bounded by the response defect. -/
theorem sq_sourceGradientAverage_sub_descendantsAverage_le_defect
    {d : ℕ} [NeZero d] {K : ℝ} (a : Coefficient d K) (Q : TriadicCube d)
    (j k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
        (regularCoefficient a).toFun i -
      descendantsAverage Q j (fun R =>
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun i)) ^ 2 ≤
    (4 * d) *
      (descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
       Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q) := by
  exact (sq_sourceGradientAverage_sub_descendantsAverage_le_meanMismatch a Q j p q i).trans
    (descendantsAverage_sourceGradientMismatch_le_four_mul_dim_mul_defect a Q j k hk p q)

end EinsteinFull.Homogenization
