import EinsteinFull.Homogenization.BlockEnergyIntegrability
import Homogenization.CoarseGraining.Translation

/-!
# Translation of Dirichlet energies

The Dirichlet energy of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (1.7),
is covariant under simultaneous translation of domain and coefficient field.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Translating the domain is equivalent to translating the coefficient field
in the opposite variational problem. -/
theorem sourceDirichletEnergy_translateSet {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volumeMeasureOn U)] (z e : Vec d) :
    EinsteinRelation.External.AKM.sourceDirichletEnergy a (translateSet z U) e =
      EinsteinRelation.External.AKM.sourceDirichletEnergy (translateCoefficient z a) U e := by
  have hopen : IsOpen (translateSet z U) := by
    rw [← preimage_subRight_eq_translateSet]
    exact hU.preimage (continuous_id.sub continuous_const)
  let : IsFiniteMeasure (volumeMeasureOn (translateSet z U)) := by
    apply isFiniteMeasure_restrict.mpr
    rw [volume_translateSet_eq]
    exact isFiniteMeasure_restrict.mp inferInstance
  rw [sourceDirichletEnergy_eq_Mu a hopen e,
    sourceDirichletEnergy_eq_Mu (translateCoefficient z a) hU e,
    Mu_translateSet_eq_translateCoeffField]
  congr 1
  funext x
  simp [translateCoeffField, translateCoefficient, add_comm]
  congr 1

end EinsteinFull.Homogenization
