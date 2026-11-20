import EinsteinFull.Homogenization.SourceResponseDecrement

/-!
# Response decrement across scales

The sum of the additivity defects controls the change in the expected response
across scales, as used in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, equation (2.44).
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The expected response decrement between two scales is bounded by the sum
of the intervening unit-loading additivity defects. -/
theorem expected_sourceResponseJ_sub_le_sum_tau
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (m n k : ℕ) (hmn : m ≤ n) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (m : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (m : ℤ))) k hk) p q ∂P) -
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) ≤
      ∑ j ∈ Finset.Ico m n, sourceResponseTau P j k hk := by
  let f : ℕ → ℝ := fun j => ∫ a, Book.Ch02.responseJ
    (Book.Ch02.cubeDomain (originCube d (j : ℤ)))
    (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (j : ℤ))) k hk) p q ∂P
  change f m - f n ≤ ∑ j ∈ Finset.Ico m n, sourceResponseTau P j k hk
  have hsum : (∑ j ∈ Finset.Ico m n, (f j - f (j + 1))) = f m - f n := by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
        rw [Finset.sum_Ico_succ_top hmn, ih]
        ring
  rw [← hsum]
  exact Finset.sum_le_sum (fun j _ => sourceResponseDecrement_le_tau hK P j k hk p q hp hq)

end EinsteinFull.Homogenization
