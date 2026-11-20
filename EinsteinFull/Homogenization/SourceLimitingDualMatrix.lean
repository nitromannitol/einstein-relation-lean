import EinsteinFull.Homogenization.SourceAnnealedDualMatrix
import EinsteinFull.Homogenization.SourceDualCoarseBound

/-!
# Limiting annealed dual matrix

The dual-energy limit in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, is represented by a
positive definite matrix without an isotropy assumption.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The polarization of the limiting expected dual energy. -/
noncomputable def limitingAnnealedDualMatrix {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) : Mat d := fun i j =>
  (⨅ n : ℕ, ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
    (Pi.single i 1 + Pi.single j 1) ∂P) -
  (⨅ n : ℕ, ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
    (Pi.single i 1) ∂P) -
  (⨅ n : ℕ, ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
    (Pi.single j 1) ∂P)

/-- The limiting dual matrix is symmetric. -/
theorem limitingAnnealedDualMatrix_isSymm {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) : (limitingAnnealedDualMatrix P).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [limitingAnnealedDualMatrix, add_comm (Pi.single j 1) (Pi.single i 1)]
  ring

/-- The entries of the annealed dual matrices converge to the limiting matrix. -/
theorem tendsto_annealedDualMatrix_entry {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Tendsto (fun n : ℕ => annealedDualMatrix P n k hk i j) atTop
      (𝓝 (limitingAnnealedDualMatrix P i j)) :=
  tendsto_expected_sourceDualCoarseMatrix_entry P hstat k hk i j

/-- The limiting expected dual energy is represented by its polarized matrix. -/
theorem iInf_expected_sourceDualEnergy_eq_matrix {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (q : Vec d) :
    (⨅ n : ℕ, ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) =
    (1 / 2 : ℝ) * vecDot q (matVecMul (limitingAnnealedDualMatrix P) q) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  have hleft := tendsto_expected_sourceDualEnergy P hstat q
  have hright := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
    (tendsto_finsetSum Finset.univ fun i _ =>
      (tendsto_const_nhds (x := q i)).mul
        (tendsto_finsetSum Finset.univ fun j _ =>
          (tendsto_annealedDualMatrix_entry P hstat k hk' i j).mul_const (q j)))
  apply tendsto_nhds_unique hleft
  refine hright.congr' (Filter.Eventually.of_forall fun n => ?_)
  simpa only [vecDot, matVecMul] using
    (expected_sourceDualEnergy_eq_annealedDualMatrix P n k hk' q).symm

/-- The limiting annealed dual matrix remains positive definite. -/
theorem limitingAnnealedDualMatrix_posDef {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P) :
    (limitingAnnealedDualMatrix P).PosDef := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using limitingAnnealedDualMatrix_isSymm P
  · intro q hq
    have hqpos : 0 < vecNormSq q :=
      lt_of_le_of_ne (vecNormSq_nonneg q) (Ne.symm (mt vecNormSq_eq_zero hq))
    have hbound := iInf_expected_sourceDualEnergy_lower k hk' P hstat q
    rw [iInf_expected_sourceDualEnergy_eq_matrix P hstat q] at hbound
    have hc : 0 < (4 * ((k : ℝ) + 1))⁻¹ := by positivity
    have hp : 0 < (4 * ((k : ℝ) + 1))⁻¹ * vecNormSq q := mul_pos hc hqpos
    have : 0 < vecDot q (matVecMul (limitingAnnealedDualMatrix P) q) := by linarith
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using this

end EinsteinFull.Homogenization
