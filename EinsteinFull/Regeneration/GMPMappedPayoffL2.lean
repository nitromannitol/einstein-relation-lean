import EinsteinFull.Regeneration.GMPDiscountedPayoffL2

/-!
# L² convergence of mapped slab payoffs

The zero-discount L² argument remains valid after a measurable change of
starting point, including the unit-force spatial rescaling.
-/

open Filter MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Measurably mapped discounted payoffs converge in L² for every finite measure. -/
theorem gmp_discounted_slab_payoff_mapped_L2_tendsto
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (c y : Vec d) (N : ℝ) (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (m : Vec d → Vec d) (hm : Measurable m)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    (∀ n, Integrable (fun z =>
      (gmpDiscountedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N (a n) (m z) -
        gmpBoundedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N (m z)) ^ 2) ν) ∧
    Tendsto (fun n : ℕ => ∫ z,
      (gmpDiscountedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N (a n) (m z) -
        gmpBoundedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N (m z)) ^ 2 ∂ν) atTop (𝓝 0) := by
  let i := Renewal.forceCoord hd
  let R := l / μ
  let V := fun z => gmpBoundedSlabPayoff G i c R y N (m z)
  let Vn : ℕ → Vec d → ℝ := fun n z => gmpDiscountedSlabPayoff G i c R y N (a n) (m z)
  let F : ℕ → Vec d → ℝ := fun n z => (Vn n z - V z) ^ 2
  have hmeas (n : ℕ) : Measurable (F n) :=
    (((measurable_gmpDiscountedSlabPayoff G i c R y N (a n)).comp hm).sub
      ((measurable_gmpBoundedSlabPayoff G i c R y N).comp hm)).pow_const 2
  have hbound (n : ℕ) (z : Vec d) : 0 ≤ F n z ∧ F n z ≤ 1 := by
    have hn := gmpDiscountedSlabPayoff_mem_Icc G i c R y N (a n) (ha n) (m z)
    have hv := gmpBoundedSlabPayoff_mem_Icc G i c R y N (m z)
    have hprod := mul_nonneg
      (show 0 ≤ 1 - (Vn n z - V z) by linarith [hn.2, hv.1])
      (show 0 ≤ 1 + (Vn n z - V z) by linarith [hn.1, hv.2])
    exact ⟨sq_nonneg _, by dsimp only [F]; nlinarith⟩
  have hint (n : ℕ) : Integrable (F n) ν := by
    apply Integrable.of_bound (hmeas n).aestronglyMeasurable 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound n z).1]
    exact (hbound n z).2
  have hpoint (z : Vec d) : Tendsto (fun n => F n z) atTop (𝓝 0) := by
    have hp : Tendsto (fun n => Vn n z) atTop (𝓝 (V z)) := by
      simpa only [Vn, V, i, R, gmpDiscountedSlabPayoff] using
        gmp_discounted_slab_payoff_tendsto d hd Λ r l hl Q μ hμ hμ1 ω hω G c y (m z) N a ha ha0
    have h := (hp.sub_const (V z)).pow 2
    simpa [F] using h
  have hlim : Tendsto (fun n : ℕ => ∫ z, F n z ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => 1)
      (fun n => (hmeas n).aestronglyMeasurable) (integrable_const 1)
      (fun n => Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound n z).1]
        exact (hbound n z).2)
      (Filter.Eventually.of_forall hpoint)
    simpa only [integral_zero] using h
  exact ⟨hint, hlim⟩

end EinsteinFull.Regeneration
