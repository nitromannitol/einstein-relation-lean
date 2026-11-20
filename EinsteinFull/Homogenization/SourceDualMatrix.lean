import EinsteinFull.Homogenization.SourceDualQuadratic
import EinsteinFull.Homogenization.SourceCoarseMatrixConvergence

/-!
# Matrix representation of dual energy

The Neumann energy in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, is represented by the
pure-flux coarse matrix, whose entries are integrable and converge in expectation.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Dual energy is the quadratic form of the pure-flux coarse matrix. -/
theorem sourceDualEnergy_eq_coarseMatrix {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (k : ℕ)
    (hK : K ≤ (k : ℝ) + 1) (q : Vec d) :
    sourceDualEnergy a U q = (1 / 2 : ℝ) * vecDot q
      (matVecMul (Book.Ch02.sigmaStarInvCoarse U (sourceCoeffOn a U k hK)) q) := by
  rw [sourceDualEnergy_eq a U k hK]
  exact (Book.Ch02.responseSymmetricDirichletNeumannTheory U (sourceCoeffOn a U k hK)
    (sourceCoeffOn_isSymmetric a U k hK)).neumann_value_by_sigmaStarInv q

/-- The pure-flux coarse matrix entries are polarized source dual energies. -/
theorem sourceDualCoarseMatrix_entry_eq_polar {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (k : ℕ)
    (hK : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Book.Ch02.sigmaStarInvCoarse U (sourceCoeffOn a U k hK) i j =
    sourceDualEnergy a U (Pi.single i 1 + Pi.single j 1) -
      sourceDualEnergy a U (Pi.single i 1) - sourceDualEnergy a U (Pi.single j 1) := by
  let M := Book.Ch02.sigmaStarInvCoarse U (sourceCoeffOn a U k hK)
  have hs : M i j = M j i := (Book.Ch02.sigmaStarInvCoarse_isSymm U (sourceCoeffOn a U k hK)).apply j i
  rw [sourceDualEnergy_eq_coarseMatrix a U k hK,
    sourceDualEnergy_eq_coarseMatrix a U k hK,
    sourceDualEnergy_eq_coarseMatrix a U k hK]
  change M i j = (1 / 2 : ℝ) * vecDot (Pi.single i 1 + Pi.single j 1)
      (matVecMul M (Pi.single i 1 + Pi.single j 1)) -
    (1 / 2 : ℝ) * vecDot (Pi.single i 1) (matVecMul M (Pi.single i 1)) -
    (1 / 2 : ℝ) * vecDot (Pi.single j 1) (matVecMul M (Pi.single j 1))
  rw [basis_sum_pairing, matVecMul_single, matVecMul_single, vecDot_single_left,
    vecDot_single_left]
  linarith

/-- Every entry of the finite-scale pure-flux coarse matrix is integrable. -/
theorem integrable_sourceDualCoarseMatrix_entry {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (n k : ℕ) (hK : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Integrable (fun a => Book.Ch02.sigmaStarInvCoarse
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hK) i j) P := by
  have h := ((integrable_sourceDualEnergy_originCube P n (Pi.single i 1 + Pi.single j 1)).sub
    (integrable_sourceDualEnergy_originCube P n (Pi.single i 1))).sub
    (integrable_sourceDualEnergy_originCube P n (Pi.single j 1))
  convert h using 1
  funext a
  exact sourceDualCoarseMatrix_entry_eq_polar a _ k hK i j

/-- Expected pure-flux coarse matrix entries converge to polarized limiting energies. -/
theorem tendsto_expected_sourceDualCoarseMatrix_entry {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hK : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Tendsto (fun n : ℕ => ∫ a, Book.Ch02.sigmaStarInvCoarse
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hK) i j ∂P)
      atTop (𝓝 ((⨅ n : ℕ, ∫ a, sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (Pi.single i 1 + Pi.single j 1) ∂P) -
        (⨅ n : ℕ, ∫ a, sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (Pi.single i 1) ∂P) -
        (⨅ n : ℕ, ∫ a, sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (Pi.single j 1) ∂P))) := by
  have h := ((tendsto_expected_sourceDualEnergy P hP (Pi.single i 1 + Pi.single j 1)).sub
    (tendsto_expected_sourceDualEnergy P hP (Pi.single i 1))).sub
    (tendsto_expected_sourceDualEnergy P hP (Pi.single j 1))
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  simp_rw [sourceDualCoarseMatrix_entry_eq_polar]
  symm
  let F : Vec d → Coefficient d K → ℝ := fun q a =>
    sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q
  have hF (q : Vec d) : Integrable (F q) P := integrable_sourceDualEnergy_originCube P n q
  change (∫ a, F (Pi.single i 1 + Pi.single j 1) a - F (Pi.single i 1) a -
    F (Pi.single j 1) a ∂P) = _
  calc
    _ = (∫ a, F (Pi.single i 1 + Pi.single j 1) a - F (Pi.single i 1) a ∂P) -
        ∫ a, F (Pi.single j 1) a ∂P :=
      integral_sub ((hF (Pi.single i 1 + Pi.single j 1)).sub (hF (Pi.single i 1)))
        (hF (Pi.single j 1))
    _ = _ := by rw [integral_sub (hF (Pi.single i 1 + Pi.single j 1)) (hF (Pi.single i 1))]

end EinsteinFull.Homogenization
