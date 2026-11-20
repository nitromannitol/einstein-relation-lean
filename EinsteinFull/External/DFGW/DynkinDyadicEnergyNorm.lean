import EinsteinFull.External.DFGW.DynkinDyadicMaximal

/-! # Norm form of the reversible maximal inequality

The stationary marginal identifies the observable's initial second moment with its `L²` norm.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A stationary evaluation of an `L²` observable has second moment equal to its squared norm. -/
theorem integral_sq_eval_eq_norm_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (t : ℝ) :
    (∫ η, f (η t) ^ 2 ∂P) = ‖f‖ ^ 2 := by
  have hi : AEStronglyMeasurable (fun x => f x ^ 2)
      (P.map (fun η : C(ℝ, S) => η t)) := by
    rw [hP.marginal]
    exact (Lp.memLp f).integrable_sq.aestronglyMeasurable
  calc
    (∫ η, f (η t) ^ 2 ∂P) = ∫ x, f x ^ 2 ∂P.map (fun η : C(ℝ, S) => η t) :=
      (integral_map (continuous_eval_const t).measurable.aemeasurable hi).symm
    _ = ∫ x, f x ^ 2 ∂μ := by rw [hP.marginal]
    _ = ‖f‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]

/-- Reversible dyadic maxima are bounded by the observable's `L²` norm and generator energy. -/
theorem measureReal_max_dynkin_dyadic_le_norm_energy
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) (a : ℝ) (ha : 0 < a) :
    (a / 4) * P.real {η | ∃ r k, k ≤ 2 ^ r ∧
      a ≤ |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|} ≤
      ‖(f : Lp ℝ 2 μ)‖ + 2 *
        Real.sqrt ((t : ℝ) *
          (2 * -inner ℝ (f : Lp ℝ 2 μ) ((transitionSemigroup hP).generator f))) := by
  have h := measureReal_max_dynkin_dyadic_le_energy hP hcoord f t a ha
  rw [integral_sq_eval_eq_norm_sq hP (f : Lp ℝ 2 μ) 0, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] at h
  exact h

end EinsteinFull.External.DFGW
