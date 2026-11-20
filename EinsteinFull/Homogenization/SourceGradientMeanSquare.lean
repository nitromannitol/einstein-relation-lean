import EinsteinFull.Homogenization.SourceGradientMeanAbsolute
import EinsteinFull.Homogenization.SourceOptimizerGradientMoments

/-!
# Mean-square convergence of averaged optimizer gradients

The averaged response gradient in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
converges in mean square to the limiting dual-matrix slope.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Each coordinate of the averaged response gradient converges in mean square
    to the slope determined by the limiting dual energy. -/
theorem integrable_and_tendsto_integral_sq_sourceResponseAverageGradient_sub_limit
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
    (∀ n, Integrable (fun a => (F n a - (-p i + ∑ j, L j * q j)) ^ 2) P) ∧
    Tendsto (fun n => ∫ a, (F n a - (-p i + ∑ j, L j * q j)) ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  intro L F
  let E : ℕ → Vec d → Coefficient d K → ℝ := fun n v a =>
    sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) v
  let H : Vec d → ℝ := fun v => ⨅ n : ℕ, ∫ a, E n v a ∂P
  let M := fun (n : ℕ) (a : Coefficient d K) (j : Fin d) =>
    Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) i j
  let B := fun j : Fin d => vecNormSq (Pi.single i 1 + Pi.single j 1) +
    vecNormSq (Pi.single i 1) + vecNormSq (Pi.single j 1)
  let C : ℝ := ∑ j : Fin d, B j * |q j|
  have hH (v : Vec d) : 0 ≤ H v ∧ H v ≤ vecNormSq v := by
    constructor
    · apply ge_of_tendsto (tendsto_expected_sourceDualEnergy P hstat v)
      exact Filter.Eventually.of_forall fun n => integral_nonneg fun a =>
        (sourceDualEnergy_originCube_bounds a n v).1
    · apply le_of_tendsto (tendsto_expected_sourceDualEnergy P hstat v)
      exact Filter.Eventually.of_forall fun n => by
        have h := integral_mono (integrable_sourceDualEnergy_originCube P n v)
          (integrable_const (vecNormSq v))
          (fun a => (sourceDualEnergy_originCube_bounds a n v).2)
        simpa only [integral_const, probReal_univ, one_smul] using h
  have hd (n : ℕ) (v : Vec d) (a : Coefficient d K) :
      |E n v a - H v| ≤ vecNormSq v := by
    have h := sourceDualEnergy_originCube_bounds a n v
    have hl := hH v
    exact abs_le.mpr ⟨by linarith [h.1, hl.2], by linarith [h.2, hl.1]⟩
  have hM (n : ℕ) (a : Coefficient d K) (j : Fin d) : |M n a j - L j| ≤ B j := by
    have heq : M n a j - L j =
        (E n (Pi.single i 1 + Pi.single j 1) a - H (Pi.single i 1 + Pi.single j 1)) -
        (E n (Pi.single i 1) a - H (Pi.single i 1)) -
        (E n (Pi.single j 1) a - H (Pi.single j 1)) := by
      dsimp only [M, L, E, H]
      rw [sourceDualCoarseMatrix_entry_eq_polar]
      ring
    rw [heq]
    exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
      (add_le_add (add_le_add (hd n _ a) (hd n _ a)) (hd n _ a))
  have hF (n : ℕ) (a : Coefficient d K) : F n a = -p i + ∑ j, M n a j * q j := by
    dsimp only [F, M]
    rw [Book.Ch02.averageGradient_canonicalMaximizer_eq]
    have hz := (Book.Ch02.responseSymmetricDirichletNeumannTheory
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (sourceCoeffOn_isSymmetric a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)).kappa_eq_zero
    simp [hz, matVecMul]
  have hbound (n : ℕ) (a : Coefficient d K) :
      |F n a - (-p i + ∑ j, L j * q j)| ≤ C := by
    rw [hF]
    have heq : (-p i + ∑ j, M n a j * q j) - (-p i + ∑ j, L j * q j) =
        ∑ j : Fin d, (M n a j - L j) * q j := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [heq]
    calc
      _ ≤ ∑ j : Fin d, |M n a j - L j| * |q j| := by
        simpa only [abs_mul] using (Finset.abs_sum_le_sum_abs
          (fun j : Fin d => (M n a j - L j) * q j) Finset.univ)
      _ ≤ C := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hM n a j) (abs_nonneg _))
  have habs := integrable_and_tendsto_integral_abs_sourceResponseAverageGradient_sub_limit
    hK P hP hstat k hk p q i
  change (∀ n, Integrable (fun a => |F n a - (-p i + ∑ j, L j * q j)|) P) ∧
    Tendsto (fun n => ∫ a, |F n a - (-p i + ∑ j, L j * q j)| ∂P) atTop (𝓝 0) at habs
  have hsquare (n : ℕ) : Integrable (fun a => (F n a - (-p i + ∑ j, L j * q j)) ^ 2) P := by
    have h := (memLp_sourceResponseAverageGradient_cube P (originCube d (n : ℤ))
      k hk p q i 2).sub (memLp_const (-p i + ∑ j, L j * q j))
    exact h.integrable_sq
  refine ⟨hsquare, ?_⟩
  have hlim := (tendsto_const_nhds (x := C)).mul habs.2
  simp only [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => integral_nonneg fun _ => sq_nonneg _) ?_
  intro n
  calc
    _ ≤ ∫ a, C * |F n a - (-p i + ∑ j, L j * q j)| ∂P := by
      apply integral_mono (hsquare n) ((habs.1 n).const_mul C)
      intro a
      nlinarith [hbound n a, abs_nonneg (F n a - (-p i + ∑ j, L j * q j)),
        sq_abs (F n a - (-p i + ∑ j, L j * q j))]
    _ = _ := integral_const_mul C _

end EinsteinFull.Homogenization
