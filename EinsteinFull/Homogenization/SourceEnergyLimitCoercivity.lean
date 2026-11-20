import EinsteinFull.Homogenization.SourceEnergyCoercivity

/-!
# Coercivity of the limiting annealed matrix

The limiting expected Dirichlet energy of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
is uniformly coercive.
-/

open MeasureTheory
open _root_.Homogenization
open EinsteinRelation (euclideanSq)

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The expected Dirichlet energy inherits the triadic coercivity bound. -/
theorem expected_sourceDirichletEnergy_triadic_lower {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n : ℕ) (e : Vec d) :
    (1 / 4 : ℝ) * euclideanSq e ≤
      ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P := by
  have h := integral_mono (integrable_const ((1 / 4 : ℝ) * euclideanSq e))
    (integrable_sourceDirichletEnergy hK P n e)
    (fun a => sourceDirichletEnergy_triadic_lower a n e)
  simpa using h

/-- The matrix of limiting expected energies has a positive quadratic lower bound. -/
theorem limitingAnnealedDirichletMatrix_lower {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (e : Vec d) :
    (1 / 2 : ℝ) * euclideanSq e ≤
      vecDot e (matVecMul (limitingAnnealedDirichletMatrix hK P hP) e) := by
  have h : (1 / 4 : ℝ) * euclideanSq e ≤
      ⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P :=
    le_ciInf fun n => expected_sourceDirichletEnergy_triadic_lower hK P n e
  rw [iInf_expected_sourceDirichletEnergy_eq_matrix hK P hP e] at h
  linarith

end EinsteinFull.Homogenization
