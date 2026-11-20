import EinsteinFull.Homogenization.SourceDirichletMatrix

/-!
# Polarization of Dirichlet energy

The polarization of the Dirichlet energy in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
is bilinear in the affine loading.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The polarization of the Dirichlet energy is additive in its first argument. -/
theorem sourceDirichletEnergy_polar_add_left {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (x y z : Vec d) :
    sourceDirichletEnergy a U (x + y + z) - sourceDirichletEnergy a U (x + y) -
        sourceDirichletEnergy a U z =
      (sourceDirichletEnergy a U (x + z) - sourceDirichletEnergy a U x -
        sourceDirichletEnergy a U z) +
      (sourceDirichletEnergy a U (y + z) - sourceDirichletEnergy a U y -
        sourceDirichletEnergy a U z) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  simp only [sourceDirichletEnergy_eq_coarseMatrix a U k hK, matVecMul_add,
    vecDot_add_left, vecDot_add_right]
  ring

/-- The polarization of the Dirichlet energy is homogeneous in its first argument. -/
theorem sourceDirichletEnergy_polar_smul_left {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (c : ℝ) (x y : Vec d) :
    sourceDirichletEnergy a U (c • x + y) - sourceDirichletEnergy a U (c • x) -
        sourceDirichletEnergy a U y =
      c * (sourceDirichletEnergy a U (x + y) - sourceDirichletEnergy a U x -
        sourceDirichletEnergy a U y) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  simp only [sourceDirichletEnergy_eq_coarseMatrix a U k hK, matVecMul_add,
    matVecMul_smul, vecDot_add_left, vecDot_add_right, vecDot_smul_left,
    vecDot_smul_right]
  ring

end EinsteinFull.Homogenization
