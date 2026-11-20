import EinsteinFull.Homogenization.SourceResponseDescendantStationarity

/-!
# One-sided response fluctuations

Subadditivity and finite-range concentration give an upper fluctuation estimate
for the response relative to its mean at a smaller scale. This is an ingredient
in the quantitative subadditive theory of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The positive deviation of a response above the mean at a smaller scale
is controlled by the finite-range fluctuations of its descendant average. -/
theorem eLpNorm_posPart_sourceResponseJ_sub_mean_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (m : ℝ) (hm : 1 ≤ m) :
    eLpNorm (fun a => max 0 (Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P))
      (ENNReal.ofReal m) P ≤
      ENNReal.ofReal (((((3 : ℝ) ^ d) ^ j)⁻¹) *
        ((Fintype.card (Fin d → ZMod 3) : ℝ) *
          EinsteinRelation.Probability.hoeffdingMomentConst m ^ (1 / m) *
          ((((3 : ℝ) ^ d) ^ j) *
            ((K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q) ^ 2) ^
            (1 / 2 : ℝ))) := by
  have hmeas : Measurable (fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q) :=
    ((measurable_sourceResponseJ_cube Q k hk p q).mono
    (coefficientLocalSigma_le_coefficientSigma _) le_rfl)
  have hbound := eLpNorm_descendantsAverage_sourceResponseJ_sub_mean_le
    hK P hP hstat Q j n hscale k hk p q m hm
  refine (eLpNorm_mono ((measurable_const.max (hmeas.sub measurable_const)).aestronglyMeasurable)
    (fun a => ?_)).trans hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _), Real.norm_eq_abs]
  apply max_le
  · exact abs_nonneg _
  · exact (sub_le_sub_right (sourceResponseJ_le_descendantsAverage a Q j k hk p q) _).trans
      (le_abs_self _)

end EinsteinFull.Homogenization
