import EinsteinFull.Homogenization.SourceAnnealedDualMatrix
import EinsteinFull.Homogenization.SourceResponseAnnealed
import Homogenization.Ambient.CoefficientField

/-!
# Minimizing the annealed response

The inverse expected dual matrix gives the unique minimizing flux for the
expected response in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, (2.45)–(2.46).
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Completing the square identifies the minimizing flux for the expected
response and its excess as the expected dual energy of the flux difference. -/
theorem expected_sourceResponseJ_eq_min_add_dualEnergy
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let M := annealedDualMatrix P n k hk
    let q₀ := matVecMul M⁻¹ p
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) =
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q₀ ∂P) +
    ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q - q₀) ∂P := by
  intro M q₀
  have hunit := (Matrix.isUnit_iff_isUnit_det (A := M)).mp
    (annealedDualMatrix_posDef P n k hk).isUnit
  have hMq₀ : matVecMul M q₀ = p := by
    dsimp only [q₀]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv M hunit]
    exact Matrix.one_mulVec p
  have hsym := annealedDualMatrix_isSymm P n k hk
  change M.IsSymm at hsym
  have hcross := vecDot_matVecMul_comm_of_isSymm hsym q q₀
  rw [hMq₀] at hcross
  have hcross' := vecDot_comm q p
  have hexpand : vecDot (q - q₀) (matVecMul M (q - q₀)) =
      vecDot q (matVecMul M q) - 2 * vecDot p q + vecDot q₀ p := by
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg,
      vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right, hMq₀]
    linarith
  rw [expected_sourceResponseJ_eq hK P n k hk p q,
    expected_sourceResponseJ_eq hK P n k hk p q₀,
    expected_sourceDualEnergy_eq_annealedDualMatrix P n k hk q,
    expected_sourceDualEnergy_eq_annealedDualMatrix P n k hk q₀,
    expected_sourceDualEnergy_eq_annealedDualMatrix P n k hk (q - q₀)]
  change _ = _ + (1 / 2 : ℝ) * vecDot (q - q₀) (matVecMul M (q - q₀))
  rw [hexpand, hMq₀, vecDot_comm q₀ p]
  ring

/-- The expected response is minimized by the inverse annealed dual matrix,
and its excess is bounded by the squared flux difference. -/
theorem expected_sourceResponseJ_min_le_and_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let M := annealedDualMatrix P n k hk
    let q₀ := matVecMul M⁻¹ p
    let R := fun v => ∫ a, Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p v ∂P
    (∀ v, Integrable (fun a => Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p v) P) ∧
    R q₀ ≤ R q ∧ R q ≤ R q₀ + vecNormSq (q - q₀) := by
  intro M q₀ R
  have heq := expected_sourceResponseJ_eq_min_add_dualEnergy hK P n k hk p q
  change R q = R q₀ + ∫ a, sourceDualEnergy a
    (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q - q₀) ∂P at heq
  have hnonneg : 0 ≤ ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q - q₀) ∂P :=
    integral_nonneg fun a => (sourceDualEnergy_originCube_bounds a n (q - q₀)).1
  have hupper := integral_mono (integrable_sourceDualEnergy_originCube P n (q - q₀))
    (integrable_const (vecNormSq (q - q₀)))
    (fun a => (sourceDualEnergy_originCube_bounds a n (q - q₀)).2)
  simp only [integral_const, probReal_univ, one_smul] at hupper
  exact ⟨fun v => integrable_sourceResponseJ hK P n k hk p v, by linarith, by linarith⟩


/-- The minimizing flux of the expected response is unique. -/
theorem expected_sourceResponseJ_eq_min_iff
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let M := annealedDualMatrix P n k hk
    let q₀ := matVecMul M⁻¹ p
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) =
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q₀ ∂P) ↔ q = q₀ := by
  intro M q₀
  constructor
  · intro heq
    have hcomplete := expected_sourceResponseJ_eq_min_add_dualEnergy hK P n k hk p q
    change _ = _ + ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q - q₀) ∂P at hcomplete
    rw [heq] at hcomplete
    have hzero : (∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) (q - q₀) ∂P) = 0 := by linarith
    have hbound := expected_sourceDualEnergy_originCube_lower k hk P (n : ℤ) (q - q₀)
    rw [hzero] at hbound
    have hc : 0 < (4 * ((k : ℝ) + 1))⁻¹ := by positivity
    have hnorm : vecNormSq (q - q₀) = 0 := by
      have := vecNormSq_nonneg (q - q₀)
      nlinarith
    exact sub_eq_zero.mp (vecNormSq_eq_zero hnorm)
  · intro h
    rw [h]

end EinsteinFull.Homogenization
