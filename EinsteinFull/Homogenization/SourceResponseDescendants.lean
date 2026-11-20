import EinsteinFull.Homogenization.SourceResponseConcentration

/-!
# Fluctuations of descendant response averages

The finite-range moment estimate for same-scale response energies applies to
the triadic descendant partitions used in the subadditive response theory of
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Chapter 2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- A centered average of responses on descendants has a finite-range
Hoeffding moment bound. -/
theorem eLpNorm_descendantsAverage_centered_sourceResponseJ_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (m : ℝ) (hm : 1 ≤ m) :
    eLpNorm (fun a => descendantsAverage Q j (fun R =>
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn b (Book.Ch02.cubeDomain R) k hk) p q ∂P))
      (ENNReal.ofReal m) P ≤
      ENNReal.ofReal (((((3 : ℝ) ^ d) ^ j)⁻¹) *
        ((Fintype.card (Fin d → ZMod 3) : ℝ) *
          EinsteinRelation.Probability.hoeffdingMomentConst m ^ (1 / m) *
          ((((3 : ℝ) ^ d) ^ j) *
            ((K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q) ^ 2) ^
            (1 / 2 : ℝ))) := by
  classical
  let D := descendantsAtDepth Q j
  let F : D → TriadicCube d := fun R => R
  have hFscale : ∀ R : D, (F R).scale = n := by
    intro R
    have h := scale_eq_sub_of_mem_descendantsAtDepth R.property
    dsimp [F] at h ⊢
    rw [h, hscale]
    simp
  have hFinj : Function.Injective fun R : D => (F R).index := by
    intro R S h
    apply Subtype.ext
    cases hr : R.val with
    | mk sr ir =>
      cases hs : S.val with
      | mk ss is =>
        have hsc : sr = ss := by
          have hR := hFscale R
          have hS := hFscale S
          dsimp [F] at hR hS
          rw [hr] at hR
          rw [hs] at hS
          exact hR.trans hS.symm
        have hi : ir = is := by simpa [F, hr, hs] using h
        cases hsc
        cases hi
        rfl
  have h := eLpNorm_sum_centered_sourceResponseJ_le hK P hP F n hFscale hFinj k hk p q m hm
  have hcard : (Fintype.card D : ℝ) = ((3 : ℝ) ^ d) ^ j := by
    simp [D, descendantsAtDepth_card]
  rw [hcard] at h
  let G : Coefficient d K → ℝ := fun a => ∑ R : D,
    (Book.Ch02.responseJ (Book.Ch02.cubeDomain (F R))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (F R)) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (F R))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (F R)) k hk) p q ∂P)
  let c : ℝ := (((3 : ℝ) ^ d) ^ j)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have havg : (fun a => descendantsAverage Q j (fun R =>
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn b (Book.Ch02.cubeDomain R) k hk) p q ∂P)) = c • G := by
    funext a
    simp only [descendantsAverage, Pi.smul_apply, smul_eq_mul, G, F, D, c,
      descendantsAtDepth_card, Nat.cast_pow, Nat.cast_ofNat]
    congr 1
    symm
    exact Finset.sum_coe_sort (descendantsAtDepth Q j) (fun R : TriadicCube d =>
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn b (Book.Ch02.cubeDomain R) k hk) p q ∂P)
  rw [havg, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
  change ENNReal.ofReal c * eLpNorm G (ENNReal.ofReal m) P ≤ ENNReal.ofReal (c * _)
  rw [ENNReal.ofReal_mul hc]
  exact mul_le_mul_right h _

end EinsteinFull.Homogenization
