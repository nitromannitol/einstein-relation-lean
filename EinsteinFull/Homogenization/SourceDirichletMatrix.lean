import EinsteinFull.Homogenization.SourceResponseBridge

/-!
# Matrix representation of Dirichlet energy

The Dirichlet energy in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, is represented by the
upper-left block of the coarse matrix.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The source Dirichlet energy is the upper-left coarse quadratic form. -/
theorem sourceDirichletEnergy_eq_coarseMatrix {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (k : ℕ)
    (hK : K ≤ (k : ℝ) + 1) (e : Vec d) :
    EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) e =
      (1 / 2 : ℝ) * vecDot e
        (matVecMul (Book.Ch02.coarseBlockMatrix U (sourceCoeffOn a U k hK)).upperLeft e) := by
  rw [sourceDirichletEnergy_eq_ResponseJ a U k hK e,
    ← Internal.Ch02.book_responseJ_eq_ResponseJ]
  have h := Internal.Ch02.BookCh02.responseJ_eq_block_quadratic U
    (sourceCoeffOn a U k hK) (-e) 0
  simpa [blockVecDot, blockMatVecMul, matVecMul, vecDot] using h

end EinsteinFull.Homogenization
