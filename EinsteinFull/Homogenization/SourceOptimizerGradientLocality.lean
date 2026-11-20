import EinsteinFull.Homogenization.SourceDualMatrix
import EinsteinFull.Homogenization.SourceResponseIndependence

/-!
# Locality of averaged optimizer gradients

For symmetric coefficients, the averaged response optimizer gradient in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Chapter 2, is determined by the dual energy on its cube.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- A pure-flux coarse matrix entry is measurable from the coefficients on its cube. -/
theorem measurable_sourceDualCoarseMatrix_entry_cube {d : ℕ} [NeZero d] {K : ℝ}
    (Q : TriadicCube d) (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    @Measurable (Coefficient d K) ℝ (localSigma (cubeSet Q)) _
      (fun a => Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) i j) := by
  have h := ((measurable_sourceDualEnergy_cube (K := K) Q (Pi.single i 1 + Pi.single j 1)).sub
    (measurable_sourceDualEnergy_cube (K := K) Q (Pi.single i 1))).sub
    (measurable_sourceDualEnergy_cube (K := K) Q (Pi.single j 1))
  convert h using 1
  funext a
  exact sourceDualCoarseMatrix_entry_eq_polar a _ k hk i j

/-- Each coordinate of the response optimizer's whole-cube average gradient is
measurable from the coefficients on that cube. -/
theorem measurable_sourceResponseAverageGradient_cube {d : ℕ} [NeZero d] {K : ℝ}
    (Q : TriadicCube d) (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    @Measurable (Coefficient d K) ℝ (localSigma (cubeSet Q)) _
      (fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
            (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution i) := by
  have hm : @Measurable (Coefficient d K) ℝ (localSigma (cubeSet Q)) _
      (fun a => -p i + ∑ j : Fin d, Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) i j * q j) := by
    exact measurable_const.add (Finset.measurable_fun_sum _ (fun j _ =>
      (measurable_sourceDualCoarseMatrix_entry_cube Q k hk i j).mul measurable_const))
  convert hm using 1
  funext a
  rw [Book.Ch02.averageGradient_canonicalMaximizer_eq]
  have hzero := (Book.Ch02.responseSymmetricDirichletNeumannTheory
    (Book.Ch02.cubeDomain Q) (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
    (sourceCoeffOn_isSymmetric a (Book.Ch02.cubeDomain Q) k hk)).kappa_eq_zero
  simp [hzero, matVecMul]

/-- Whole-cube optimizer gradient coordinates on separated cubes are jointly independent. -/
theorem iIndepFun_sourceResponseAverageGradient_of_separated {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] {K : ℝ} (P : Measure (Coefficient d K))
    [IsProbabilityMeasure P] (hP : AKMFiniteRange P) (s : ℝ) (hs : 1 < s)
    (Q : ι → TriadicCube d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ cubeSet (Q i), ∀ y ∈ cubeSet (Q j),
      s ≤ EinsteinRelation.euclideanNorm (x - y))
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : ι → Vec d) (coord : ι → Fin d) :
    ProbabilityTheory.iIndepFun (fun i a => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (Q i)) (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (Q i))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk)) (p i) (q i)).toSolution
        (coord i)) P := by
  let X := fun i a => Book.Ch02.averageGradient
    (Book.Ch02.cubeDomain (Q i)) (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk)
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (Q i))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk)) (p i) (q i)).toSolution
      (coord i)
  have hI := iIndep_coefficient_localSigma_of_separated P hP s hs
    (fun i => cubeSet (Q i)) (fun i => measurableSet_cubeSet (Q i)) hsep
  refine (ProbabilityTheory.iIndepFun_iff_iIndep (fun _ : ι => Real.measurableSpace) X P).mpr ?_
  rw [ProbabilityTheory.iIndep_iff]
  intro S f hf
  have hH : ∀ i ∈ S, MeasurableSet[localSigma (cubeSet (Q i))] (f i) := fun i hi =>
    (measurable_iff_comap_le.mp
      (measurable_sourceResponseAverageGradient_cube (Q i) k hk (p i) (q i) (coord i))) _
      (hf i hi)
  exact (ProbabilityTheory.iIndep_iff _ P).mp hI S hH

end EinsteinFull.Homogenization
