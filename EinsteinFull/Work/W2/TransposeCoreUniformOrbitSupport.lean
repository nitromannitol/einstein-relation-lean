import EinsteinFull.Work.W2.TransposeGeneratorCoreApproximationSupport

/-!
# Uniform approximation of actual transpose orbits

The structural semigroup bound propagates the all-data normalized resolvent
approximation uniformly through every finite time interval, including zero.
Full weak graph transport proves resolvent commutation on arbitrary L2 data.
-/

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- Every actual shifted transpose resolvent commutes with the actual evolution,
without a domain assumption on the datum. -/
theorem IsComplexTransposeSemigroup.resolvent_commute
    (hT : IsComplexTransposeSemigroup Q P T)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    T t (complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) f) =
      complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) (T t f) := by
  have hg := hT.map_generator hP
    (complexL2Transpose_forcedComplexResolvent_spec Q i ζ s hs f) t
  have he := (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs _ _).mp hg
  simpa only [map_sub, map_smul, sub_sub_cancel] using he.symm

/-- The normalization remains exactly n+1 above the structural force shift. -/
theorem IsComplexTransposeSemigroup.resolventApproximation_commute
    (hT : IsComplexTransposeSemigroup Q P T)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (n : ℕ) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    T t (complexTransposeResolventApproximation Q i ζ n f) =
      complexTransposeResolventApproximation Q i ζ n (T t f) := by
  simp only [complexTransposeResolventApproximation_eq, ContinuousLinearMap.smul_apply,
    map_smul, hT.resolvent_commute hP]

/-- A single structural constant controls the error at every time up to H,
including time zero, for every complex L2 initial datum. -/
theorem IsComplexTransposeSemigroup.orbit_approximation_error_le
    (hT : IsComplexTransposeSemigroup Q P T)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (H : ℝ≥0) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (ht : t ≤ H) :
    ‖T t (complexTransposeResolventApproximation Q i ζ n f) - T t f‖ ≤
      Real.exp (complexForceShift d Λ₀ ζ * (H : ℝ)) *
        ‖complexTransposeResolventApproximation Q i ζ n f - f‖ := by
  rw [← map_sub]
  apply ((T t).le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (hT.norm_le hP t).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ H from ht)
      (complexForceShift_nonneg Q ζ)))

/-- Actual normalized transpose core orbits converge uniformly on every compact
nonnegative time interval for arbitrary L2 data. -/
theorem IsComplexTransposeSemigroup.tendstoUniformlyOn_resolventApproximation
    (hT : IsComplexTransposeSemigroup Q P T)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (H : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    TendstoUniformlyOn
      (fun n t => T t (complexTransposeResolventApproximation Q i ζ n f))
      (fun t => T t f) atTop (Set.Icc 0 H) := by
  have hz := ((tendsto_complexTransposeResolventApproximation Q i ζ f).sub_const f).norm.const_mul
    (Real.exp (complexForceShift d Λ₀ ζ * (H : ℝ)))
  simp only [sub_self, norm_zero, mul_zero] at hz
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hz.eventually (gt_mem_nhds hε)] with n hn
  intro t ht
  rw [dist_eq_norm, norm_sub_rev]
  exact (hT.orbit_approximation_error_le hP H n f t ht.2).trans_lt hn

end EinsteinFull
