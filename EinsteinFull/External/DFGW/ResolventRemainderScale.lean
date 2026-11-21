import EinsteinFull.External.DFGW.ResolventRemainderBound

/-! # Sublinear resolvent remainder on comparable scales

The Kipnis–Varadhan mean-square remainder is sublinear along any sequence of times comparable
with the reciprocal resolvent parameter.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The normalized mean-square remainder vanishes along any sequence between half and all of
the reciprocal resolvent scale. -/
theorem tendsto_resolvent_remainder_comparable (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (q : ℕ → ℝ≥0)
    (hlower : ∀ n, (1 / 2 : ℝ) ≤ (reciprocalShift n : ℝ) * (q n : ℝ))
    (hupper : ∀ n, (reciprocalShift n : ℝ) * (q n : ℝ) ≤ 1) :
    Tendsto (fun n : ℕ => (q n : ℝ)⁻¹ * ‖timeIntegralLp hP f (q n) - Z (q n)‖ ^ 2)
      atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun n => (reciprocalShift n : ℝ) *
    ‖transitionResolvent hP (reciprocalShift n) f‖ ^ 2
  let E : ℕ → ℝ := fun n => ‖dynkinIncrementLp hP
    (transitionResolventDomain hP (reciprocalShift n) f) 1 - Z 1‖ ^ 2
  have hR : Tendsto R atTop (𝓝 0) := tendsto_reciprocalShift_mul_resolvent_norm_sq hP f hint
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := ((hZ 1).sub_const (Z 1)).norm.pow 2
    simpa [E] using h
  have hlim : Tendsto (fun n : ℕ => 36 * R n + 4 * E n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hR.const_mul 36).add (hE.const_mul 4)
  apply squeeze_zero (g := fun n : ℕ => 36 * R n + 4 * E n)
  · intro n
    exact mul_nonneg (inv_nonneg.mpr (q n).coe_nonneg) (sq_nonneg _)
  · intro n
    exact norm_resolvent_remainder_le hP hcoord f Z hZ n (q n) (hlower n) (hupper n)
  · exact hlim

end EinsteinFull.External.DFGW
