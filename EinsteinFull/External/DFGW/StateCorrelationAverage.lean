import EinsteinFull.External.DFGW.StateMeanErgodic
import EinsteinFull.External.DFGW.TwoTimeCorrelation

/-! # Averaged state correlations

The correlations of two square-integrable stationary state observables, averaged over any
positive time grid, converge to the product of their means.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Averaged state correlations converge to the product of the means. -/
theorem tendsto_average_state_correlation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t) (f g : Lp ℝ 2 μ) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      inner ℝ f (transitionOperator hP (k • t) g)) atTop
      (𝓝 ((∫ x, f x ∂μ) * (∫ x, g x ∂μ))) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let U := transitionOperator hP t
  have hit (n : ℕ) : U^[n] g = transitionOperator hP (n • t) g := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, zero_nsmul, transitionOperator_zero,
        ContinuousLinearMap.id_apply]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, succ_nsmul, add_comm (n • t) t,
        transitionOperator_add]
      rfl
  dsimp only [U] at hit
  have hmean := tendsto_transitionOperator_birkhoffAverage hP hμ ht g
  have hcont : Continuous (fun x : Lp ℝ 2 μ => inner ℝ f x) :=
    continuous_const.inner continuous_id
  have h := (hcont.tendsto
    (indicatorConstLp 2 MeasurableSet.univ hμ (∫ x, g x ∂μ))).comp hmean
  have hval : inner ℝ f (indicatorConstLp 2 MeasurableSet.univ hμ (∫ x, g x ∂μ)) =
      (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
    rw [L2.inner_def, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := hμ) (c := ∫ x, g x ∂μ)] with x hx
    simp only [Set.indicator_univ] at hx
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, mul_comm]
  rw [hval] at h
  convert h using 1
  funext n
  simp only [Function.comp_apply, birkhoffAverage, birkhoffSum, id_eq, inner_smul_right,
    inner_sum, hit]

end EinsteinFull.External.DFGW
