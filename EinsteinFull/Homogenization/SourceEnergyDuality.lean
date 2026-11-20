import EinsteinFull.Homogenization.SourceDualAnnealed
import EinsteinFull.Homogenization.SourceEnergyAnnealed
import EinsteinFull.Homogenization.SourceDirichletQuadratic
import Homogenization.Book.Ch02.Theorems.MatrixPositivity

/-!
# Dirichlet and dual energy inequality

Nonnegativity of the response gives the duality inequality for the subadditive
quantities in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, (2.6).
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The primal and dual energies dominate the pairing of their loadings. -/
theorem vecDot_le_sourceDirichletEnergy_add_sourceDualEnergy {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (p q : Vec d) :
    vecDot p q ≤ sourceDirichletEnergy a (U : Set (Vec d)) p + sourceDualEnergy a U q := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  have hnonneg := Book.Ch02.responseJ_nonneg U (sourceCoeffOn a U k hK) p q
  rw [responseJ_eq_sourceDirichlet_add_sourceDual] at hnonneg
  have heven : sourceDirichletEnergy a (U : Set (Vec d)) (-p) =
      sourceDirichletEnergy a (U : Set (Vec d)) p := by
    simpa using sourceDirichletEnergy_smul a U (-1) p
  rw [heven] at hnonneg
  linarith

/-- The duality inequality survives averaging over a probability law. -/
theorem vecDot_le_expected_sourceDirichletEnergy_add_sourceDualEnergy
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (n : ℕ) (p q : Vec d) :
    vecDot p q ≤
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) p ∂P) +
      ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P := by
  have hdir := integrable_sourceDirichletEnergy hK P n p
  have hdual := integrable_sourceDualEnergy_originCube P n q
  have h := integral_mono (integrable_const (vecDot p q)) (hdir.add hdual)
    (fun a => by
      change vecDot p q ≤ sourceDirichletEnergy a (sourceTriadicCube d n) p +
        sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q
      simpa only [Book.Ch02.cubeDomain_coe, ← sourceTriadicCube_eq_openCubeSet] using
        vecDot_le_sourceDirichletEnergy_add_sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (n : ℤ))) p q)
  change (∫ _a, vecDot p q ∂P) ≤
    ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) p +
      sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P at h
  simpa only [integral_const, probReal_univ, one_smul, integral_add hdir hdual] using h

/-- The limiting primal and dual energies dominate the pairing of the loadings. -/
theorem vecDot_le_iInf_expected_sourceDirichletEnergy_add_sourceDualEnergy
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (p q : Vec d) :
    vecDot p q ≤
      (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) p ∂P) +
      ⨅ n : ℕ, ∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P := by
  have hlim := (tendsto_expected_sourceDirichletEnergy hK P hP p).add
    (tendsto_expected_sourceDualEnergy P hP q)
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall
    (fun n => vecDot_le_expected_sourceDirichletEnergy_add_sourceDualEnergy hK P n p q))

end EinsteinFull.Homogenization
