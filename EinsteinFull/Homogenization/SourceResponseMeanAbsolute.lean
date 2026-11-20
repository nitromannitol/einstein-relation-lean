import EinsteinFull.Homogenization.SourceResponseUpperFluctuation

/-!
# Mean absolute response fluctuations

The one-sided concentration estimate and the gap between expected energies
control the mean absolute deviation. This is the subadditive argument in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Proposition 1.7.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The mean absolute deviation of a parent response from the mean at a smaller
scale is controlled by one-sided fluctuations and the gap of expected responses. -/
theorem integral_abs_sourceResponseJ_sub_mean_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    (∫ a, |Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P| ∂P) ≤
    2 * (((((3 : ℝ) ^ d) ^ j)⁻¹) *
      ((Fintype.card (Fin d → ZMod 3) : ℝ) *
        EinsteinRelation.Probability.hoeffdingMomentConst 1 ^ (1 / (1 : ℝ)) *
        ((((3 : ℝ) ^ d) ^ j) *
          ((K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q) ^ 2) ^
          (1 / 2 : ℝ))) +
      (∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P) -
      ∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P := by
  let f := fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P
  have hf : Integrable f P := (integrable_sourceResponseJ_cube hK P Q k hk p q).sub
    (integrable_const _)
  have hp : Integrable (fun a => max 0 (f a)) P := by
    simpa only [max_comm] using hf.pos_part
  have hbound := eLpNorm_posPart_sourceResponseJ_sub_mean_le hK P hP hstat
    Q j n hscale k hk p q 1 (by norm_num)
  change eLpNorm (fun a => max 0 (f a)) (ENNReal.ofReal 1) P ≤ _ at hbound
  rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hp.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hp] at hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  have hC : 0 ≤ EinsteinRelation.Probability.hoeffdingMomentConst 1 := by
    unfold EinsteinRelation.Probability.hoeffdingMomentConst
    positivity
  rw [ENNReal.toReal_ofReal (integral_nonneg fun a => norm_nonneg _),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hpbound := hreal
  have hnorm : ∀ a, ‖max 0 (f a)‖ = max 0 (f a) := by
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 (f a))]
  simp_rw [hnorm] at hpbound
  have habs := integral_abs_eq_two_mul_integral_posPart_sub_integral hf
  have hint : (∫ a, f a ∂P) =
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P) -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P := by
    dsimp only [f]
    rw [integral_sub (integrable_sourceResponseJ_cube hK P Q k hk p q) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  simp only [PosPart.posPart, max_comm] at habs
  change (∫ a, |f a| ∂P) ≤ _
  rw [habs, hint]
  linarith

end EinsteinFull.Homogenization
