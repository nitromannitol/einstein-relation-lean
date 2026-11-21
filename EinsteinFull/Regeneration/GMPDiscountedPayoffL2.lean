import EinsteinFull.Regeneration.GMPDiscountedPayoff

/-!
# Spatial L² limit of discounted slab payoffs

Pointwise zero-discount convergence and unit bounds imply convergence of
the squared difference on every finite-volume set.
-/

open Filter MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Discounted slab payoffs converge in spatial L² on finite-volume sets. -/
theorem gmp_discounted_slab_payoff_L2_tendsto
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (c y : Vec d) (N : ℝ) (U : Set (Vec d))
    [IsFiniteMeasure (volume.restrict U : Measure (Vec d))]
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    (∀ n, IntegrableOn (fun z =>
      (gmpDiscountedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N (a n) z -
        gmpBoundedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N z) ^ 2) U) ∧
    Tendsto (fun n : ℕ => ∫ z in U,
      (gmpDiscountedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N (a n) z -
        gmpBoundedSlabPayoff G (Renewal.forceCoord hd) c (l / μ) y N z) ^ 2) atTop (𝓝 0) := by
  let i := Renewal.forceCoord hd
  let R := l / μ
  let V := gmpBoundedSlabPayoff G i c R y N
  let Vn : ℕ → Vec d → ℝ := fun n => gmpDiscountedSlabPayoff G i c R y N (a n)
  let F : ℕ → Vec d → ℝ := fun n z => (Vn n z - V z) ^ 2
  have hmeas (n : ℕ) : Measurable (F n) :=
    ((measurable_gmpDiscountedSlabPayoff G i c R y N (a n)).sub
      (measurable_gmpBoundedSlabPayoff G i c R y N)).pow_const 2
  have hbound (n : ℕ) (z : Vec d) : 0 ≤ F n z ∧ F n z ≤ 1 := by
    have hn := gmpDiscountedSlabPayoff_mem_Icc G i c R y N (a n) (ha n) z
    have hv := gmpBoundedSlabPayoff_mem_Icc G i c R y N z
    have hprod := mul_nonneg
      (show 0 ≤ 1 - (Vn n z - V z) by linarith [hn.2, hv.1])
      (show 0 ≤ 1 + (Vn n z - V z) by linarith [hn.1, hv.2])
    exact ⟨sq_nonneg _, by dsimp only [F]; nlinarith⟩
  have hint (n : ℕ) : IntegrableOn (F n) U := by
    apply Integrable.of_bound (hmeas n).aestronglyMeasurable 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound n z).1]
    exact (hbound n z).2
  have hpoint (z : Vec d) : Tendsto (fun n => F n z) atTop (𝓝 0) := by
    have hp : Tendsto (fun n => Vn n z) atTop (𝓝 (V z)) := by
      simpa only [Vn, V, i, R, gmpDiscountedSlabPayoff] using
        gmp_discounted_slab_payoff_tendsto d hd Λ r l hl Q μ hμ hμ1 ω hω G c y z N a ha ha0
    have h := (hp.sub_const (V z)).pow 2
    simpa [F] using h
  have hlim : Tendsto (fun n : ℕ => ∫ z, F n z ∂(volume.restrict U)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict U) (fun _ => 1)
      (fun n => (hmeas n).aestronglyMeasurable) (integrable_const 1)
      (fun n => Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound n z).1]
        exact (hbound n z).2)
      (Filter.Eventually.of_forall hpoint)
    simpa only [integral_zero] using h
  exact ⟨hint, hlim⟩

end EinsteinFull.Regeneration
