import EinsteinFull.Homogenization.SourceDualAnnealed

/-!
# Coercivity of dual energy

The dual subadditive quantity in Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 2, has a
scale-independent positive lower bound determined by the ellipticity ratio.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The dual energy controls its flux loading uniformly on triadic cubes. -/
theorem sourceDualEnergy_originCube_lower {d : ℕ} [NeZero d] {K : ℝ}
    (k : ℕ) (hK : K ≤ (k : ℝ) + 1) (a : Coefficient d K) (m : ℤ) (q : Vec d) :
    (4 * ((k : ℝ) + 1))⁻¹ * vecNormSq q ≤
      sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d m)) q := by
  let Q := originCube d m
  let U := Book.Ch02.cubeDomain Q
  let A := unitLowerSourceCoeffOn a U k hK
  let A' := Internal.Ch02.BookCh02.pointwiseCoeffField U A
  have hEll : IsEllipticFieldOn 1 ((k : ℝ) + 1) (cubeSet Q) A' :=
    Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet Q A
  have hlower := diag_lower_le_mu_cube hEll (0, q)
  have hae : A' =ᵐ[volumeMeasureOn (openCubeSet Q)] (regularCoefficient a).toFun := by
    simpa [A', A, U, unitLowerSourceCoeffOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U A
  have heq : Mu (cubeSet Q) (0, q) A' = sourceDualEnergy a U q := by
    rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube Q (0, q) A',
      Mu_congr_of_ae_eq hae (0, q)]
    exact (sourceDualEnergy_eq_Mu a U q).symm
  rw [heq] at hlower
  simpa [vecNormSq, vecDot] using hlower

/-- The expected dual energy has the same uniform coercive bound. -/
theorem expected_sourceDualEnergy_originCube_lower {d : ℕ} [NeZero d] {K : ℝ}
    (k : ℕ) (hK : K ≤ (k : ℝ) + 1) (P : Measure (Coefficient d K))
    [IsProbabilityMeasure P] (m : ℤ) (q : Vec d) :
    (4 * ((k : ℝ) + 1))⁻¹ * vecNormSq q ≤
      ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d m)) q ∂P := by
  have h := integral_mono (integrable_const ((4 * ((k : ℝ) + 1))⁻¹ * vecNormSq q))
    (integrable_sourceDualEnergy_originCube P m q)
    (fun a => sourceDualEnergy_originCube_lower k hK a m q)
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- The limiting expected dual energy retains the uniform coercive bound. -/
theorem iInf_expected_sourceDualEnergy_lower {d : ℕ} [NeZero d] {K : ℝ}
    (k : ℕ) (hK : K ≤ (k : ℝ) + 1) (P : Measure (Coefficient d K))
    [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (q : Vec d) :
    (4 * ((k : ℝ) + 1))⁻¹ * vecNormSq q ≤
      ⨅ n : ℕ, ∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P := by
  exact ge_of_tendsto (tendsto_expected_sourceDualEnergy P hP q)
    (Filter.Eventually.of_forall fun n => expected_sourceDualEnergy_originCube_lower k hK P n q)

end EinsteinFull.Homogenization
