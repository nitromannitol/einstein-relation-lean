import EinsteinFull.Homogenization.SourceOptimizerGradientMean
import Mathlib.Probability.Moments.Variance

/-!
# Fluctuations of averaged optimizer gradients

The averaged dual-maximizer gradient of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
has vanishing variance at large triadic scales.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Each coordinate of the averaged dual-maximizer gradient at a basis loading
has variance tending to zero. -/
theorem tendsto_variance_averageGradient_dualMaximizer
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Tendsto (fun n : ℕ => ProbabilityTheory.variance (fun a =>
      Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
            (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk))
          0 (Pi.single j 1)).toSolution i) P) atTop (𝓝 0) := by
  let E : ℕ → Vec d → Coefficient d K → ℝ := fun n q a =>
    sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q
  let L : Vec d → ℝ := fun q => ⨅ n : ℕ, ∫ a, E n q a ∂P
  let e₁ : Vec d := Pi.single i 1
  let e₂ : Vec d := Pi.single j 1
  let B : ℝ := vecNormSq (e₁ + e₂) + vecNormSq e₁ + vecNormSq e₂
  let X : ℕ → Coefficient d K → ℝ := fun n a =>
    Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) i j
  let l : ℝ := L (e₁ + e₂) - L e₁ - L e₂
  have hL (q : Vec d) : 0 ≤ L q ∧ L q ≤ vecNormSq q := by
    constructor
    · apply ge_of_tendsto (tendsto_expected_sourceDualEnergy P hstat q)
      exact Filter.Eventually.of_forall fun n => integral_nonneg fun a =>
        (sourceDualEnergy_originCube_bounds a n q).1
    · apply le_of_tendsto (tendsto_expected_sourceDualEnergy P hstat q)
      exact Filter.Eventually.of_forall fun n => by
        have h := integral_mono (integrable_sourceDualEnergy_originCube P n q)
          (integrable_const (vecNormSq q))
          (fun a => (sourceDualEnergy_originCube_bounds a n q).2)
        simpa only [integral_const, probReal_univ, one_smul] using h
  have hd (n : ℕ) (q : Vec d) (a : Coefficient d K) :
      |E n q a - L q| ≤ vecNormSq q := by
    have h := sourceDualEnergy_originCube_bounds a n q
    have hl := hL q
    exact abs_le.mpr ⟨by linarith [h.1, hl.2], by linarith [h.2, hl.1]⟩
  have hbound (n : ℕ) (a : Coefficient d K) : |X n a - l| ≤ B := by
    have heq : X n a - l = (E n (e₁ + e₂) a - L (e₁ + e₂)) -
        (E n e₁ a - L e₁) - (E n e₂ a - L e₂) := by
      dsimp only [X, l, L, E, e₁, e₂]
      rw [sourceDualCoarseMatrix_entry_eq_polar]
      ring
    rw [heq]
    exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
      (add_le_add (add_le_add (hd n (e₁ + e₂) a) (hd n e₁ a)) (hd n e₂ a))
  have hmean : Tendsto (fun n : ℕ => ∫ a, |X n a - l| ∂P) atTop (𝓝 0) := by
    simpa only [X, l, L, E, e₁, e₂] using
      tendsto_integral_abs_sourceDualCoarseMatrix_entry_sub_limit hK P hP hstat k hk i j
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => B) atTop (𝓝 B)).mul hmean
  simp only [mul_zero] at hlim
  have hv : Tendsto (fun n : ℕ => ProbabilityTheory.variance (X n) P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => ProbabilityTheory.variance_nonneg _ _) ?_
    intro n
    have hint : Integrable (X n) P := integrable_sourceDualCoarseMatrix_entry P n k hk i j
    have hdint : Integrable (fun a => X n a - l) P := hint.sub (integrable_const l)
    have hpoint (a : Coefficient d K) : (X n a - l) ^ 2 ≤ B * |X n a - l| := by
      nlinarith [hbound n a, abs_nonneg (X n a - l), sq_abs (X n a - l)]
    have hsquare : Integrable (fun a => (X n a - l) ^ 2) P := by
      apply (hdint.abs.const_mul B).mono' (by fun_prop)
      filter_upwards [] with a
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpoint a
    have hv := ProbabilityTheory.variance_le_expectation_sq hdint.aestronglyMeasurable
    rw [ProbabilityTheory.variance_sub_const hint.aestronglyMeasurable] at hv
    calc
      _ ≤ ∫ a, (X n a - l) ^ 2 ∂P := hv
      _ ≤ ∫ a, B * |X n a - l| ∂P :=
        integral_mono hsquare (hdint.abs.const_mul B) hpoint
      _ = B * ∫ a, |X n a - l| ∂P := integral_const_mul B _
  convert hv using 1
  funext n
  congr 1
  funext a
  rw [Book.Ch02.averageGradient_canonicalMaximizer_eq]
  simp only [neg_zero, matVecMul_zero, add_zero, zero_add, matVecMul_single, X]

end EinsteinFull.Homogenization
