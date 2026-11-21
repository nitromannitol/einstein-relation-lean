import EinsteinFull.External.DFGW.ResolventRemainderBound

/-! # Sublinear resolvent remainder at all times

The Kipnis–Varadhan remainder has mean square `o(t)` as continuous time tends to infinity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The integrated observable minus its limiting resolvent martingale has mean square `o(t)`. -/
theorem tendsto_resolvent_remainder_atTop (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t))) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ‖timeIntegralLp hP f t - Z t‖ ^ 2)
      atTop (𝓝 0) := by
  let k : ℝ≥0 → ℕ := fun t => ⌊(t : ℝ)⌋₊
  let R : ℕ → ℝ := fun n => (reciprocalShift n : ℝ) *
    ‖transitionResolvent hP (reciprocalShift n) f‖ ^ 2
  let E : ℕ → ℝ := fun n => ‖dynkinIncrementLp hP
    (transitionResolventDomain hP (reciprocalShift n) f) 1 - Z 1‖ ^ 2
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop (n : ℝ≥0)] with t ht
    apply Nat.le_floor
    exact_mod_cast ht
  have hR : Tendsto R atTop (𝓝 0) := tendsto_reciprocalShift_mul_resolvent_norm_sq hP f hint
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := ((hZ 1).sub_const (Z 1)).norm.pow 2
    simpa [E] using h
  have hlim : Tendsto (fun t : ℝ≥0 => 36 * R (k t) + 4 * E (k t)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, add_zero] using ((hR.comp hk).const_mul 36).add ((hE.comp hk).const_mul 4)
  apply squeeze_zero' (Filter.Eventually.of_forall fun t =>
    mul_nonneg (inv_nonneg.mpr t.coe_nonneg) (sq_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with t ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hfloor : (k t : ℝ) ≤ t := Nat.floor_le t.coe_nonneg
  have hceil : (t : ℝ) < (k t : ℝ) + 1 := Nat.lt_floor_add_one (t : ℝ)
  have hden : 0 < (k t : ℝ) + 1 := by positivity
  have hupper : (reciprocalShift (k t) : ℝ) * t ≤ 1 := by
    change (1 / ((k t : ℝ) + 1)) * (t : ℝ) ≤ 1
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hden]
    linarith
  have hlower : (1 / 2 : ℝ) ≤ (reciprocalShift (k t) : ℝ) * t := by
    change (1 / 2 : ℝ) ≤ (1 / ((k t : ℝ) + 1)) * (t : ℝ)
    simp only [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ hden).2
    linarith
  exact norm_resolvent_remainder_le hP hcoord f Z hZ (k t) t hlower hupper

end EinsteinFull.External.DFGW
