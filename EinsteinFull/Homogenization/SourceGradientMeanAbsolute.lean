import EinsteinFull.Homogenization.SourceGradientMeanMatrix
import EinsteinFull.Homogenization.SourceDualMatrixMeanConvergence

/-!
# Mean absolute convergence of optimizer gradients

The whole-cube averaged response gradient in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
converges in mean to the limiting dual-matrix slope.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Each coordinate of the averaged response gradient converges in L¹ to
the slope determined by the limiting dual energy. -/
theorem integrable_and_tendsto_integral_abs_sourceResponseAverageGradient_sub_limit
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    let L := fun j : Fin d =>
      (⨅ m : ℕ, ∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single i 1 + Pi.single j 1) ∂P) -
      (⨅ m : ℕ, ∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single i 1) ∂P) -
      (⨅ m : ℕ, ∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single j 1) ∂P)
    let F := fun (n : ℕ) (a : Coefficient d K) => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution i
    (∀ n, Integrable (fun a => |F n a - (-p i + ∑ j, L j * q j)|) P) ∧
    Tendsto (fun n => ∫ a, |F n a - (-p i + ∑ j, L j * q j)| ∂P) atTop (𝓝 0) := by
  classical
  intro L F
  let M := fun (n : ℕ) (a : Coefficient d K) (j : Fin d) =>
    Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) i j
  have hM (n : ℕ) (j : Fin d) : Integrable (fun a => M n a j) P :=
    integrable_sourceDualCoarseMatrix_entry P n k hk i j
  have hF (n : ℕ) (a : Coefficient d K) : F n a = -p i + ∑ j, M n a j * q j := by
    dsimp only [F, M]
    rw [Book.Ch02.averageGradient_canonicalMaximizer_eq]
    have hz := (Book.Ch02.responseSymmetricDirichletNeumannTheory
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (sourceCoeffOn_isSymmetric a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)).kappa_eq_zero
    simp [hz, matVecMul]
  have hI (n : ℕ) : Integrable (F n) P :=
    (integral_sourceResponseAverageGradient_eq P n k hk p q i).1
  refine ⟨fun n => ((hI n).sub (integrable_const _)).abs, ?_⟩
  have hlim : Tendsto (fun n => ∑ j : Fin d,
      (∫ a, |M n a j - L j| ∂P) * |q j|) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun j _ =>
      (tendsto_integral_abs_sourceDualCoarseMatrix_entry_sub_limit
        hK P hP hstat k hk i j).mul_const |q j|)
    simpa only [zero_mul, Finset.sum_const_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => integral_nonneg fun _ => abs_nonneg _) ?_
  intro n
  have hbound (a : Coefficient d K) :
      |F n a - (-p i + ∑ j, L j * q j)| ≤ ∑ j : Fin d, |M n a j - L j| * |q j| := by
    rw [hF]
    have heq : (-p i + ∑ j, M n a j * q j) - (-p i + ∑ j, L j * q j) =
        ∑ j : Fin d, (M n a j - L j) * q j := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [heq]
    simpa only [abs_mul] using (Finset.abs_sum_le_sum_abs
      (fun j : Fin d => (M n a j - L j) * q j) Finset.univ)
  have hsum : Integrable (fun a => ∑ j : Fin d, |M n a j - L j| * |q j|) P :=
    integrable_finsetSum _ (fun j _ => ((hM n j).sub (integrable_const _)).abs.mul_const _)
  calc
    _ ≤ ∫ a, ∑ j : Fin d, |M n a j - L j| * |q j| ∂P :=
      integral_mono (((hI n).sub (integrable_const _)).abs) hsum hbound
    _ = _ := by
      have hs := integral_finsetSum (f := fun j a => |M n a j - L j| * |q j|)
        Finset.univ (fun j _ => ((hM n j).sub (integrable_const _)).abs.mul_const _)
      change (∫ a, ∑ j : Fin d, |M n a j - L j| * |q j| ∂P) = _ at hs
      rw [hs]
      simp only [integral_mul_const]

end EinsteinFull.Homogenization
