import EinsteinFull.Homogenization.OpenCubeEnergyMeasurability
import EinsteinFull.Homogenization.SourceDirichletTranslation
import Homogenization.Geometry.TriadicCubeTranslation

/-!
# Stationary Dirichlet energies

The translation-invariant law in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (0.10),
gives equal expected Dirichlet energies on lattice translates of a triadic cube.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Under a stationary finite law, the energy on a lattice translate is
integrable and has the same expectation as on the original triadic cube. -/
theorem sourceDirichletEnergy_stationary_expectation {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (z : LatticeIndex d)
    (hP : Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (e : Vec d) :
    Integrable (fun a => EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (translateSet (latticeShift z) (openCubeSet Q)) e) P ∧
    (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (translateSet (latticeShift z) (openCubeSet Q)) e ∂P) =
      ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a (openCubeSet Q) e ∂P := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let f : Coefficient d K → ℝ := fun a =>
    EinsteinRelation.External.AKM.sourceDirichletEnergy a (openCubeSet Q) e
  have hf : Integrable f P := integrable_sourceDirichletEnergy_openCube hK P Q e
  have hmp : MeasurePreserving (translateCoefficient (latticeShift z)) P P :=
    ⟨measurable_translateCoefficient _, hP⟩
  have hcomp : Integrable (fun a => f (translateCoefficient (latticeShift z) a)) P :=
    hmp.integrable_comp_of_integrable hf
  have hpoint (a : Coefficient d K) : EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (translateSet (latticeShift z) (openCubeSet Q)) e =
      f (translateCoefficient (latticeShift z) a) :=
    sourceDirichletEnergy_translateSet a (isOpen_openCubeSet Q) (latticeShift z) e
  constructor
  · exact hcomp.congr (ae_of_all _ fun a => (hpoint a).symm)
  · calc
      (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
          (translateSet (latticeShift z) (openCubeSet Q)) e ∂P) =
          ∫ a, f (translateCoefficient (latticeShift z) a) ∂P :=
            integral_congr_ae (ae_of_all _ hpoint)
      _ = ∫ a, f a ∂P := by
        have hmap := integral_map (measurable_translateCoefficient (latticeShift z)).aemeasurable
          (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable)
        rw [hmp.map_eq] at hmap
        exact hmap.symm

/-- At a nonnegative scale, every triadic cube is an integer translate of the
centered source cube at that scale. -/
theorem openCubeSet_eq_latticeTranslate_sourceTriadicCube {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) (hscale : Q.scale = n) :
    openCubeSet Q = translateSet
      (latticeShift (fun i => Q.index i * (3 : ℤ) ^ n))
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) := by
  rw [sourceTriadicCube_eq_openCubeSet, ← hscale,
    openCubeSet_eq_translateSet_originCube_of_triadicCube]
  congr 1
  funext i
  simp [latticeShift, triadicCubeShift, cubeScaleFactor, hscale, zpow_natCast]

/-- Stationarity makes expected Dirichlet energies independent of the cube
position at every nonnegative triadic scale. -/
theorem sourceDirichletEnergy_expected_eq_origin {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (n : ℕ) (hscale : Q.scale = n) (e : Vec d) :
    (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a (openCubeSet Q) e ∂P) =
      ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
        (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P := by
  let z : LatticeIndex d := fun i => Q.index i * (3 : ℤ) ^ n
  have h := sourceDirichletEnergy_stationary_expectation hK P z (hP z)
    (originCube d (n : ℤ)) e
  rw [← sourceTriadicCube_eq_openCubeSet d n] at h
  rw [openCubeSet_eq_latticeTranslate_sourceTriadicCube Q n hscale]
  exact h.2

end EinsteinFull.Homogenization
