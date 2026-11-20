import EinsteinFull.Homogenization.SourceResponseDescendants

/-!
# Stationary centering of descendant responses

Stationarity identifies the mean of every same-scale descendant response with
the mean at the origin, as used in the subadditive response theory of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Chapter 2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- For a stationary law, centering each descendant response agrees with
centering the descendant average by the response mean at the origin. -/
theorem descendantsAverage_centered_sourceResponseJ_eq {d : ℕ} [NeZero d]
    {K : ℝ} (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (a : Coefficient d K) :
    descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn b (Book.Ch02.cubeDomain R) k hk) p q ∂P) =
    descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P := by
  classical
  let D := descendantsAtDepth Q j
  have hD : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  have hmean : ∀ R ∈ D, (∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn b (Book.Ch02.cubeDomain R) k hk) p q ∂P) =
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P := by
    intro R hR
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hR
    have hs' : R.scale = (n : ℤ) := by rw [hs, hscale]; simp
    exact sourceResponseJ_expected_eq_origin hK P hP R n hs' k hk p q
  unfold descendantsAverage
  change (D.card : ℝ)⁻¹ * (∑ R ∈ D, (Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q -
    ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn b (Book.Ch02.cubeDomain R) k hk) p q ∂P)) = _
  rw [Finset.sum_sub_distrib]
  have heq : (∑ R ∈ D, ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn b (Book.Ch02.cubeDomain R) k hk) p q ∂P) =
      (D.card : ℝ) * (∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P) := by
    rw [Finset.sum_congr rfl (fun R hR => hmean R hR), Finset.sum_const, nsmul_eq_mul]
  rw [heq]
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]


/-- Descendant response averages satisfy the finite-range moment bound when
centered by the stationary mean at their common scale. -/
theorem eLpNorm_descendantsAverage_sourceResponseJ_sub_mean_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (m : ℝ) (hm : 1 ≤ m) :
    eLpNorm (fun a => descendantsAverage Q j (fun R =>
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P)
      (ENNReal.ofReal m) P ≤
      ENNReal.ofReal (((((3 : ℝ) ^ d) ^ j)⁻¹) *
        ((Fintype.card (Fin d → ZMod 3) : ℝ) *
          EinsteinRelation.Probability.hoeffdingMomentConst m ^ (1 / m) *
          ((((3 : ℝ) ^ d) ^ j) *
            ((K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q) ^ 2) ^
            (1 / 2 : ℝ))) := by
  have h := eLpNorm_descendantsAverage_centered_sourceResponseJ_le
    hK P hP Q j n hscale k hk p q m hm
  simp_rw [descendantsAverage_centered_sourceResponseJ_eq hK P hstat Q j n hscale k hk p q] at h
  exact h

end EinsteinFull.Homogenization
