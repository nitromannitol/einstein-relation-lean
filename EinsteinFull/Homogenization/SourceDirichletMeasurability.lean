import EinsteinFull.Homogenization.BlockEnergyIntegrability
import EinsteinFull.Homogenization.SourceTriadicCube
import EinsteinRelation.Correctors.AKMSourceDirichletUpperBound

/-!
# Measurability of the Dirichlet energy

The Dirichlet energy on the triadic cubes of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (1.7) and
(0.20), is an observable of the corresponding coefficient field.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The source Dirichlet energy on a centered cube is measurable for the
observations supported in the corresponding half-open triadic cube. -/
theorem measurable_sourceDirichletEnergy_triadic {d : ℕ} [NeZero d] {K : ℝ}
    (n : ℕ) (e : Vec d) :
    @Measurable (Coefficient d K) ℝ
      (localSigma (_root_.Homogenization.cubeSet
        (_root_.Homogenization.originCube d (n : ℤ)))) _
      (fun a => External.AKM.sourceDirichletEnergy a (External.AKM.sourceTriadicCube d n) e) := by
  have hU : IsOpen (External.AKM.sourceTriadicCube d n) := by
    rw [sourceTriadicCube_eq_openCubeSet]
    exact _root_.Homogenization.isOpen_openCubeSet _
  let : IsFiniteMeasure (_root_.Homogenization.volumeMeasureOn
      (External.AKM.sourceTriadicCube d n)) := by
    rw [sourceTriadicCube_eq_openCubeSet]
    simpa [_root_.Homogenization.volumeMeasureOn] using
      (_root_.Homogenization.isOpenBoundedConvexDomain_openCubeSet
        (_root_.Homogenization.originCube d (n : ℤ))).isFiniteMeasure_restrict_volume
  have h := measurable_regularCoefficient_Mu_sourceTriadicCube (K := K) n (e, 0)
  convert h using 1
  funext a
  exact sourceDirichletEnergy_eq_Mu_regularCoefficient a hU e

/-- The Dirichlet energy is measurable for the full coefficient sigma algebra. -/
theorem measurable_sourceDirichletEnergy {d : ℕ} [NeZero d] {K : ℝ}
    (n : ℕ) (e : Vec d) :
    Measurable (fun a : Coefficient d K =>
      External.AKM.sourceDirichletEnergy a (External.AKM.sourceTriadicCube d n) e) :=
  (measurable_sourceDirichletEnergy_triadic n e).mono
    (coefficientLocalSigma_le_coefficientSigma _) le_rfl

/-- Under every finite law, the Dirichlet energy on a triadic cube is integrable. -/
theorem integrable_sourceDirichletEnergy {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (n : ℕ) (e : Vec d) :
    Integrable (fun a => External.AKM.sourceDirichletEnergy a
      (External.AKM.sourceTriadicCube d n) e) P :=
  External.AKM.integrable_sourceDirichletEnergy_of_aestronglyMeasurable hK P n e
    (measurable_sourceDirichletEnergy n e).aestronglyMeasurable

end EinsteinFull.Homogenization
