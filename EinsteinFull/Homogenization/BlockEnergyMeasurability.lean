import EinsteinFull.Homogenization.CoefficientEllipticity

/-!
# Local measurability of block energies

The coefficient observations of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (0.11),
make the block energy on each triadic cube locally measurable.
-/

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The block energy of the regular representative is measurable for the
source local coefficient sigma algebra on every half-open triadic cube. -/
theorem measurable_regularCoefficient_Mu {d : ℕ} {K : ℝ}
    (Q : _root_.Homogenization.TriadicCube d) (P : _root_.Homogenization.BlockVec d) :
    @Measurable (Coefficient d K) ℝ (localSigma (_root_.Homogenization.cubeSet Q)) _
      (fun a => _root_.Homogenization.Mu (_root_.Homogenization.cubeSet Q) P
        (regularCoefficient a).toFun) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  apply _root_.Homogenization.measurable_Mu_comp_aeeSlice_of_measurable_entryTest Q
    (regularCoefficient_aeeQuantitativeEllipticSlice
      (_root_.Homogenization.cubeSet Q) (_root_.Homogenization.measurableSet_cubeSet Q) k hk')
  intro i j φ hφ hφc hφQ
  exact measurable_entryTestR_regularCoefficient (_root_.Homogenization.cubeSet Q)
    ⟨φ, hφ, hφc⟩ hφQ i j

end EinsteinFull.Homogenization
