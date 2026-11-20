import EinsteinFull.Homogenization.SourceDualBlockBridge
import EinsteinFull.Homogenization.SourceDualAnnealed
import Homogenization.Book.Ch02.Theorems.Quadraticity

/-!
# Quadraticity of dual energy

The dual subadditive quantity in Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 2, is quadratic
in its loading, both before and after averaging.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The dual energy is homogeneous of degree two in the loading. -/
theorem sourceDualEnergy_smul {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (c : ℝ) (q : Vec d) :
    sourceDualEnergy a U (c • q) = c ^ 2 * sourceDualEnergy a U q := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  have hvalue (v : Vec d) : Book.Ch02.responseJ U (sourceCoeffOn a U k hK) 0 v =
      sourceDualEnergy a U v := by
    have h := responseJ_eq_sourceDirichlet_add_sourceDual a U k hK 0 v
    have hzero : EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) 0 = 0 := by
      simpa using sourceDirichletEnergy_smul a U 0 (0 : Vec d)
    simpa [hzero, vecDot] using h
  have h := Book.Ch02.responseJ_smul (a := sourceCoeffOn a U k hK) c 0 q
  simpa only [smul_zero, hvalue] using h

/-- The dual energy satisfies the parallelogram identity. -/
theorem sourceDualEnergy_parallelogram {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (q₁ q₂ : Vec d) :
    sourceDualEnergy a U (q₁ + q₂) + sourceDualEnergy a U (q₁ - q₂) =
      2 * sourceDualEnergy a U q₁ + 2 * sourceDualEnergy a U q₂ := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  have hvalue (v : Vec d) : Book.Ch02.responseJ U (sourceCoeffOn a U k hK) 0 v =
      sourceDualEnergy a U v := by
    have h := responseJ_eq_sourceDirichlet_add_sourceDual a U k hK 0 v
    have hzero : EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) 0 = 0 := by
      simpa using sourceDirichletEnergy_smul a U 0 (0 : Vec d)
    simpa [hzero, vecDot] using h
  have h := Book.Ch02.responseJ_parallelogram (a := sourceCoeffOn a U k hK) 0 q₁ 0 q₂
  simpa only [zero_add, sub_self, hvalue] using h

/-- Expected dual energies are homogeneous of degree two. -/
theorem expected_sourceDualEnergy_smul {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (n : ℕ) (c : ℝ) (q : Vec d) :
    (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (c • q) ∂P) =
      c ^ 2 * ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P := by
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (fun a => sourceDualEnergy_smul a _ c q))

/-- Expected dual energies satisfy the parallelogram identity. -/
theorem expected_sourceDualEnergy_parallelogram {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (n : ℕ) (q₁ q₂ : Vec d) :
    (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q₁ + q₂) ∂P) +
    (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q₁ - q₂) ∂P) =
    2 * (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q₁ ∂P) +
    2 * (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q₂ ∂P) := by
  have h := integral_congr_ae (ae_of_all P (fun a => sourceDualEnergy_parallelogram a
    (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q₁ q₂))
  rw [integral_add (integrable_sourceDualEnergy_originCube P n (q₁ + q₂))
      (integrable_sourceDualEnergy_originCube P n (q₁ - q₂)),
    integral_add ((integrable_sourceDualEnergy_originCube P n q₁).const_mul 2)
      ((integrable_sourceDualEnergy_originCube P n q₂).const_mul 2),
    integral_const_mul, integral_const_mul] at h
  exact h

/-- The limiting expected dual energy is homogeneous of degree two. -/
theorem iInf_expected_sourceDualEnergy_smul {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (c : ℝ) (q : Vec d) :
    (⨅ n : ℕ, ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (c • q) ∂P) =
    c ^ 2 * (⨅ n : ℕ, ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) := by
  have hleft := tendsto_expected_sourceDualEnergy P hP (c • q)
  have hright := (tendsto_const_nhds (x := c ^ 2)).mul
    (tendsto_expected_sourceDualEnergy P hP q)
  apply tendsto_nhds_unique hleft
  refine hright.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (expected_sourceDualEnergy_smul P n c q).symm

/-- The limiting expected dual energy satisfies the parallelogram identity. -/
theorem iInf_expected_sourceDualEnergy_parallelogram {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (q₁ q₂ : Vec d) :
    (⨅ n : ℕ, ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q₁ + q₂) ∂P) +
    (⨅ n : ℕ, ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q₁ - q₂) ∂P) =
    2 * (⨅ n : ℕ, ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q₁ ∂P) +
    2 * (⨅ n : ℕ, ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q₂ ∂P) := by
  have hleft := (tendsto_expected_sourceDualEnergy P hP (q₁ + q₂)).add
    (tendsto_expected_sourceDualEnergy P hP (q₁ - q₂))
  have hright := ((tendsto_const_nhds (x := (2 : ℝ))).mul
    (tendsto_expected_sourceDualEnergy P hP q₁)).add
    ((tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_expected_sourceDualEnergy P hP q₂))
  apply tendsto_nhds_unique hleft
  refine hright.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (expected_sourceDualEnergy_parallelogram P n q₁ q₂).symm

end EinsteinFull.Homogenization
