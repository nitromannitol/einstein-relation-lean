import EinsteinFull.Homogenization.SourceEnergyLimitPolar

/-!
# Quadratic form of the limiting annealed energy

The limiting expected Dirichlet energy in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
defines a quadratic form on the affine loadings.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The quadratic form whose value is the limiting expected Dirichlet energy. -/
noncomputable def limitingAnnealedDirichletForm {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P) :
    QuadraticForm ℝ (Vec d) :=
  QuadraticMap.ofPolar
    (fun e => ⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P)
    (by
      intro c e
      simpa only [pow_two, smul_eq_mul] using
        iInf_expected_sourceDirichletEnergy_smul hK P hP c e)
    (by
      intro x y z
      simpa only [QuadraticMap.polar] using
        iInf_expected_sourceDirichletEnergy_polar_add_left hK P hP x y z)
    (by
      intro c x y
      simpa only [QuadraticMap.polar, smul_eq_mul] using
        iInf_expected_sourceDirichletEnergy_polar_smul_left hK P hP c x y)

/-- Evaluation of the limiting form gives the source's limiting energy. -/
theorem limitingAnnealedDirichletForm_apply {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (e : Vec d) :
    limitingAnnealedDirichletForm hK P hP e =
      ⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P := rfl

end EinsteinFull.Homogenization
