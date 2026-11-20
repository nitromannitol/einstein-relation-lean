import EinsteinFull.Homogenization.SourceOptimizerGradientLocality

/-!
# Mean response optimizer gradient

For symmetric coefficients, the mean optimizer gradient in Armstrong, Kuusi
and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2, is expressed by the mean dual coarse matrix.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- For symmetric coefficients the mean response gradient is the affine
function of the expected dual coarse matrix given in (2.43). -/
theorem integral_sourceResponseAverageGradient_eq
    {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    let U := Book.Ch02.cubeDomain (originCube d (n : ℤ))
    let M := fun a : Coefficient d K => Book.Ch02.sigmaStarInvCoarse U
      (sourceCoeffOn a U k hk)
    let F := fun a : Coefficient d K => Book.Ch02.averageGradient U
      (sourceCoeffOn a U k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U (sourceCoeffOn a U k hk)) p q).toSolution i
    Integrable F P ∧ (∀ j, Integrable (fun a => M a i j) P) ∧
      (∫ a, F a ∂P) = -p i + ∑ j : Fin d, (∫ a, M a i j ∂P) * q j := by
  classical
  intro U M F
  have hM (j : Fin d) : Integrable (fun a => M a i j) P :=
    integrable_sourceDualCoarseMatrix_entry P n k hk i j
  have hF : ∀ a, F a = -p i + ∑ j : Fin d, M a i j * q j := by
    intro a
    dsimp only [F, M, U]
    rw [Book.Ch02.averageGradient_canonicalMaximizer_eq]
    have hz := (Book.Ch02.responseSymmetricDirichletNeumannTheory
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (sourceCoeffOn_isSymmetric a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)).kappa_eq_zero
    simp [hz, matVecMul]
  have hsum : Integrable (fun a => ∑ j : Fin d, M a i j * q j) P :=
    integrable_finsetSum _ (fun j _ => (hM j).mul_const (q j))
  refine ⟨?_, hM, ?_⟩
  · have heq : F = fun a => -p i + ∑ j : Fin d, M a i j * q j := funext hF
    rw [heq]
    exact (integrable_const _).add hsum
  · simp_rw [hF]
    rw [integral_add (integrable_const _) hsum]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    rw [integral_finsetSum _ (fun j _ => (hM j).mul_const (q j))]
    simp only [integral_mul_const]

/-- The mean optimizer gradient converges to the limiting dual-matrix slope. -/
theorem tendsto_integral_sourceResponseAverageGradient
    {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    Tendsto (fun n : ℕ => ∫ a, Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution i ∂P)
      atTop (𝓝 (-p i + ∑ j : Fin d,
        ((⨅ m : ℕ, ∫ a, sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single i 1 + Pi.single j 1) ∂P) -
         (⨅ m : ℕ, ∫ a, sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single i 1) ∂P) -
         (⨅ m : ℕ, ∫ a, sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single j 1) ∂P)) * q j)) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => -p i) atTop (𝓝 (-p i))).add
    (tendsto_finsetSum Finset.univ (fun j _ =>
    (tendsto_expected_sourceDualCoarseMatrix_entry P hstat k hk i j).mul_const (q j)))
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (integral_sourceResponseAverageGradient_eq P n k hk p q i).2.2.symm

end EinsteinFull.Homogenization
