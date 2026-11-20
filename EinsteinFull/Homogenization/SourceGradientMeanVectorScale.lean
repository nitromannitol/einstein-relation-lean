import EinsteinFull.Homogenization.SourceGradientMeanScale

/-!
# Mean vector gradient across scales

The mean optimizer gradient satisfies the cross-scale bound of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, equation (2.44).
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The squared change in the mean optimizer gradient is bounded by the sum
of the intervening response defects, with an explicit dimension constant. -/
theorem integrable_and_vecNormSq_integral_sourceGradient_sub_le_sum_tau
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (m n k : ℕ) (hmn : m ≤ n) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    let F := fun (r : ℕ) (i : Fin d) (a : Coefficient d K) =>
      Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
            (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)) p q).toSolution i
    (∀ r i, Integrable (F r i) P) ∧
    vecNormSq (fun i => (∫ a, F n i a ∂P) - (∫ a, F m i a ∂P)) ≤
      (4 * (d : ℝ) ^ 2) * ∑ j ∈ Finset.Ico m n, sourceResponseTau P j k hk := by
  classical
  intro F
  refine ⟨fun r i => (sq_integral_sourceGradient_sub_le_sum_tau
    hK P hstat m n k hmn hk p q hp hq i).1 r, ?_⟩
  have hb (i : Fin d) : ((∫ a, F n i a ∂P) - (∫ a, F m i a ∂P)) ^ 2 ≤
      (4 * d) * ∑ j ∈ Finset.Ico m n, sourceResponseTau P j k hk :=
    (sq_integral_sourceGradient_sub_le_sum_tau hK P hstat m n k hmn hk p q hp hq i).2
  unfold vecNormSq vecDot
  calc
    _ = ∑ i : Fin d, ((∫ a, F n i a ∂P) - (∫ a, F m i a ∂P)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (sq _).symm
    _ ≤ ∑ _i : Fin d, (4 * (d : ℝ)) *
        ∑ j ∈ Finset.Ico m n, sourceResponseTau P j k hk := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end EinsteinFull.Homogenization
