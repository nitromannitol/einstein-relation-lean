import EinsteinFull.Homogenization.SourceGradientMeanDefect

/-!
# Mean gradient on descendants

Stationarity identifies the mean of the descendant optimizer gradients with
that of a single optimizer on the origin cube, as in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
equation (2.44).
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The expected descendant average is the expected origin-cube gradient. -/
theorem integral_descendantsAverage_sourceGradient_eq_origin
    {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    (∫ a, descendantsAverage Q j (fun R =>
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun i) ∂P) =
    ∫ a, Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution i ∂P := by
  classical
  let X := fun R a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
    (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution i
  simp_rw [sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)]
  change (∫ a, descendantsAverage Q j (fun R => X R a) ∂P) =
    ∫ a, X (originCube d (n : ℤ)) a ∂P
  unfold descendantsAverage
  rw [integral_const_mul, integral_finsetSum _ (fun R _ =>
    (memLp_sourceResponseAverageGradient_cube P R k hk p q i 2).integrable (by norm_num))]
  have hn : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  have hmean (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
      (∫ a, X R a ∂P) = ∫ a, X (originCube d (n : ℤ)) a ∂P := by
    apply integral_sourceResponseAverageGradient_eq_origin P hstat R n k ?_ hk p q i
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hscale]
    simp
  rw [Finset.sum_congr rfl (fun R hR => hmean R hR), Finset.sum_const, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end EinsteinFull.Homogenization
