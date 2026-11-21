import EinsteinFull.External.DFGW.StateMixing
import EinsteinFull.External.DFGW.TransitionConstant

/-! # Mixing of state correlations

The transition semigroup converges in `L²` to the stationary mean along positive time grids.
Consequently, correlations of square-integrable state observables converge to products of means.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Positive-time transition iterates converge in `L²` to the stationary mean. -/
theorem tendsto_transitionOperator_grid
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    Tendsto (fun n : ℕ => transitionOperator hP (n • t) f) atTop
      (𝓝 (indicatorConstLp 2 MeasurableSet.univ hμ (∫ x, f x ∂μ))) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let c : ℝ := ∫ x, f x ∂μ
  let k : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ hμ c
  have hk : k =ᵐ[μ] fun _ => c := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := hμ) (c := c)] with x hx
    simpa only [k, Set.indicator_univ] using hx
  have hkint : ∫ x, k x ∂μ = c := by
    rw [integral_congr_ae hk]
    simp
  have hcenter : ∫ x, (f - k) x ∂μ = 0 := by
    rw [integral_congr_ae (Lp.coeFn_sub f k)]
    change (∫ x, (f x - k x) ∂μ) = 0
    rw [integral_sub ((Lp.memLp f).integrable one_le_two)
      ((Lp.memLp k).integrable one_le_two), hkint]
    exact sub_self c
  have h := tendsto_transitionOperator_grid_of_integral_eq_zero hP hμ ht (f - k) hcenter
  have hadd : Tendsto (fun n : ℕ => transitionOperator hP (n • t) (f - k) + k)
      atTop (𝓝 (0 + k)) := h.add tendsto_const_nhds
  have heq (n : ℕ) : transitionOperator hP (n • t) (f - k) + k =
      transitionOperator hP (n • t) f := by
    rw [map_sub, transitionOperator_indicator_univ hP hμ c]
    abel
  simp only [zero_add] at hadd
  simpa only [heq] using hadd

/-- State correlations converge to the product of the stationary means. -/
theorem tendsto_state_correlation_grid
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t) (f g : Lp ℝ 2 μ) :
    Tendsto (fun n : ℕ => inner ℝ f (transitionOperator hP (n • t) g)) atTop
      (𝓝 ((∫ x, f x ∂μ) * (∫ x, g x ∂μ))) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have hcont : Continuous (fun x : Lp ℝ 2 μ => inner ℝ f x) :=
    continuous_const.inner continuous_id
  have h := (hcont.tendsto
    (indicatorConstLp 2 MeasurableSet.univ hμ (∫ x, g x ∂μ))).comp
      (tendsto_transitionOperator_grid hP hμ ht g)
  have hval : inner ℝ f (indicatorConstLp 2 MeasurableSet.univ hμ (∫ x, g x ∂μ)) =
      (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
    rw [L2.inner_def, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := hμ) (c := ∫ x, g x ∂μ)] with x hx
    simp only [Set.indicator_univ] at hx
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, mul_comm]
  simpa only [Function.comp_def, hval] using h

end EinsteinFull.External.DFGW
