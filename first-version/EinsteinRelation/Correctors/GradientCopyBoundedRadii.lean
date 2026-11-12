import EinsteinRelation.Correctors.CanonicalGradientMomentBounds
import EinsteinRelation.Correctors.CanonicalGradientCopyMoments

/-! # Bounded physical radii in the gradient-copy estimate

Source: `paper/main.tex:859–862,878–886`. Lemma 5.1 and the two copy
marginals control every bounded interval of radii. Thus the sharp copy
estimate only needs an analytic proof above any fixed parameter-dependent
threshold, including the physical finite-range scale.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance boundedRadiusRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The actual point-gradient copy bound at radii above a fixed threshold
extends to every radius at least one. Its constant still precedes the
environment law, radius, center and column. No independence of the two
copies is used. Source: `paper/main.tex:859–862,878–886`. -/
theorem gradientCopy_decay_of_large_radii
    (H51 : CorrectorGradientMoments) (d : ℕ) (hd : 2 ≤ d)
    (L r₀ m S : ℝ) (hm : 2 ≤ m) (hS : 1 ≤ S)
    (hlarge : ∃ C₀ : ℝ, ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), S ≤ R →
      ∀ (y : Point d) (i : Fin d),
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
        (FieldPair d × FieldPair d) =>
        euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
          conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (C₀ * R ^ (-(d : ℝ) / 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R →
      ∀ (y : Point d) (i : Fin d),
      let Z := fun z : C(conditionalCorrectorBall R y, Mat d) ×
        (FieldPair d × FieldPair d) =>
        euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
          conditionalCorrectorGradient Q i y z.2.2)
      MemLp Z (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ∧
      eLpNorm Z (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)) := by
  obtain ⟨C₀, hC₀⟩ := hlarge
  obtain ⟨G, hG, hGb⟩ := exists_canonicalGradient_moment_bound H51 hd L r₀ hm
  let C := max C₀ 0 + 2 * G * S ^ ((d : ℝ) / 2) + 1
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q R hR y i
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hGb' : eLpNorm (fun ω => euclideanNorm (conditionalCorrectorGradient Q i 0 ω))
      (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal G := by
    simpa only [conditionalCorrectorGradient, WithLp.ofLp_zero] using hGb Q i
  obtain ⟨hmem, hbound⟩ := canonicalGradientCopy_moment_le Q i y
    (conditionalCorrectorBall R y) (isOpen_conditionalCorrectorBall R y)
    (ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ m)) hG hGb'
  refine ⟨hmem, ?_⟩
  by_cases hSR : S ≤ R
  · refine (hC₀ Q R hSR y i).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hRp.le _)
    dsimp only [C]
    linarith [le_max_left C₀ 0, mul_nonneg (show 0 ≤ 2 * G by positivity)
      (Real.rpow_nonneg hSp.le ((d : ℝ) / 2))]
  · have hpow : 1 ≤ S ^ ((d : ℝ) / 2) * R ^ (-(d : ℝ) / 2) := by
      calc
        1 = S ^ ((d : ℝ) / 2) * S ^ (-(d : ℝ) / 2) := by
          rw [← Real.rpow_add hSp]
          rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero]
        _ ≤ S ^ ((d : ℝ) / 2) * R ^ (-(d : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hSp.le _)
          exact Real.rpow_le_rpow_of_nonpos hRp (not_le.mp hSR).le
            (by linarith [Nat.cast_nonneg (α := ℝ) d])
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      2 * G ≤ (2 * G) * (S ^ ((d : ℝ) / 2) * R ^ (-(d : ℝ) / 2)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * G by positivity)
      _ = (2 * G * S ^ ((d : ℝ) / 2)) * R ^ (-(d : ℝ) / 2) := by ring
      _ ≤ C * R ^ (-(d : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hRp.le _)
        dsimp only [C]
        linarith [le_max_right C₀ 0]

end EinsteinRelation.Correctors
