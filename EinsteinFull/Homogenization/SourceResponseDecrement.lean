import EinsteinFull.Homogenization.SourceResponseVariance

/-!
# Uniform response decrements

The additivity defect in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Section 2.2, is the supremum of
expected response decrements over unit loadings.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Values of the expected response decrement over pairs of unit-ball loadings. -/
def sourceResponseDecrementValues {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) : Set ℝ :=
  {x | ∃ p q : Vec d, vecNormSq p < 1 ∧ vecNormSq q < 1 ∧
    x = (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) -
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk) p q ∂P)}

/-- The unit-loading decrement values are nonempty. -/
theorem sourceResponseDecrementValues_nonempty {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    (sourceResponseDecrementValues P n k hk).Nonempty := by
  refine ⟨_, 0, 0, ?_, ?_, rfl⟩ <;> simp [vecNormSq, vecDot]

/-- The unit-loading decrement values are bounded above under a probability law. -/
theorem bddAbove_sourceResponseDecrementValues {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    BddAbove (sourceResponseDecrementValues P n k hk) := by
  refine ⟨K / 2 + 2, ?_⟩
  rintro x ⟨p, q, hp, hq, rfl⟩
  have hp0 := vecNormSq_nonneg p
  have habs := abs_vecDot_le_add_halves_vecNormSq p q
  have hdot : -1 ≤ vecDot p q := by
    have h := neg_le_abs (vecDot p q)
    linarith
  have heq : EinsteinRelation.euclideanSq (-p) = vecNormSq p := by
    simp [EinsteinRelation.euclideanSq, EinsteinRelation.dot, vecNormSq, vecDot]
  have hbound (a : Coefficient d K) : Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ≤ K / 2 + 2 := by
    have h := (sourceResponseJ_cube_bounds hK a (originCube d (n : ℤ)) k hk p q).2
    rw [heq] at h
    nlinarith
  have hu := integral_mono (integrable_sourceResponseJ hK P n k hk p q)
    (integrable_const (K / 2 + 2)) hbound
  simp only [integral_const, probReal_univ, one_smul] at hu
  have hl : 0 ≤ ∫ a, Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk) p q ∂P :=
    integral_nonneg fun a => Book.Ch02.responseJ_nonneg _ _ _ _
  linarith

/-- The expected response additivity defect over unit-ball loadings. -/
noncomputable def sourceResponseTau {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) : ℝ :=
  sSup (sourceResponseDecrementValues P n k hk)

/-- Each unit-loading expected response decrement is at most the additivity defect. -/
theorem sourceResponseDecrement_le_tau {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) -
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk) p q ∂P) ≤
      sourceResponseTau P n k hk := by
  exact le_csSup (bddAbove_sourceResponseDecrementValues hK P n k hk) ⟨p, q, hp, hq, rfl⟩

/-- The response additivity defect is nonnegative. -/
theorem sourceResponseTau_nonneg {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) : 0 ≤ sourceResponseTau P n k hk := by
  apply le_csSup (bddAbove_sourceResponseDecrementValues hK P n k hk)
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simp [vecNormSq, vecDot]
  · simp [vecNormSq, vecDot]
  · have hz (Q : TriadicCube d) (a : Coefficient d K) :
        Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) 0 0 = 0 := by
      have h := sourceResponseJ_cube_bounds hK a Q k hk 0 0
      have hupper : Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) 0 0 ≤ 0 := by
        simpa [EinsteinRelation.euclideanSq, EinsteinRelation.dot, vecNormSq, vecDot] using h.2
      exact le_antisymm hupper h.1
    simp [hz]

end EinsteinFull.Homogenization
