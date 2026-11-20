import EinsteinFull.Homogenization.SourceEnergyAnnealedQuadratic

/-!
# Quadraticity of the limiting annealed Dirichlet energy

The limiting expected Dirichlet energy in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
inherits the quadratic identities from finite scales.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The limit of the expected Dirichlet energy is homogeneous of degree two. -/
theorem iInf_expected_sourceDirichletEnergy_smul {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (c : ℝ) (e : Vec d) :
    (⨅ n : ℕ, ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) (c • e) ∂P) =
    c ^ 2 * (⨅ n : ℕ, ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P) := by
  have hleft := tendsto_expected_sourceDirichletEnergy hK P hP (c • e)
  have hright := (tendsto_const_nhds (x := c ^ 2)).mul (tendsto_expected_sourceDirichletEnergy hK P hP e)
  apply tendsto_nhds_unique hleft
  refine hright.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (expected_sourceDirichletEnergy_smul hK P n c e).2.symm

/-- The limit of the expected Dirichlet energy satisfies the parallelogram identity. -/
theorem iInf_expected_sourceDirichletEnergy_parallelogram {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (e₁ e₂ : Vec d) :
    (⨅ n : ℕ, ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) (e₁ + e₂) ∂P) +
    (⨅ n : ℕ, ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) (e₁ - e₂) ∂P) =
    2 * (⨅ n : ℕ, ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e₁ ∂P) +
    2 * (⨅ n : ℕ, ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e₂ ∂P) := by
  have hleft := (tendsto_expected_sourceDirichletEnergy hK P hP (e₁ + e₂)).add
    (tendsto_expected_sourceDirichletEnergy hK P hP (e₁ - e₂))
  have hright := ((tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_expected_sourceDirichletEnergy hK P hP e₁)).add
    ((tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_expected_sourceDirichletEnergy hK P hP e₂))
  apply tendsto_nhds_unique hleft
  refine hright.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (expected_sourceDirichletEnergy_parallelogram hK P n e₁ e₂).symm

end EinsteinFull.Homogenization
