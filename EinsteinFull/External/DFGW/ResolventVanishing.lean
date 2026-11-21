import EinsteinFull.External.DFGW.ResolventDifference
import EinsteinFull.External.DFGW.LaplaceLimit

/-! # Vanishing normalized resolvents

An integrable autocorrelation makes the normalized squared resolvent norm tend to zero along
reciprocal positive parameters.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The reciprocal sequence of positive Laplace parameters. -/
noncomputable def reciprocalShift (n : ℕ) : MarkovProcess.Semigroup.PositiveShift :=
  ⟨1 / ((n : ℝ) + 1), by change 0 < 1 / ((n : ℝ) + 1); positivity⟩

/-- The normalized squared resolvent norm vanishes when the autocorrelation is integrable. -/
theorem tendsto_reciprocalShift_mul_resolvent_norm_sq
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    Tendsto (fun n : ℕ => (reciprocalShift n : ℝ) * ‖transitionResolvent hP (reciprocalShift n) f‖ ^ 2)
      atTop (𝓝 0) := by
  let b : ℕ → MarkovProcess.Semigroup.PositiveShift := reciprocalShift
  let a : ℕ → MarkovProcess.Semigroup.PositiveShift := fun n =>
    ⟨(b n : ℝ) / 2, by change 0 < (b n : ℝ) / 2; exact div_pos (b n).2 (by norm_num)⟩
  let r : ℝ → ℝ := fun t => inner ℝ f (transitionOperator hP t.toNNReal f)
  have hr : Continuous r := by
    change Continuous (fun t : ℝ => inner ℝ f (transitionSemigroup hP t.toNNReal f))
    exact continuous_const.inner (((transitionSemigroup hP).continuous_orbit f).comp
      continuous_real_toNNReal)
  have hb : Tendsto (fun n => (b n : ℝ)) atTop (𝓝 0) := by
    simpa only [b, reciprocalShift] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ha : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0) := by
    simpa only [a, zero_div] using hb.div_const 2
  have hb' : Tendsto (fun n => (b n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hb, Filter.Eventually.of_forall fun n => (b n).2⟩
  have ha' : Tendsto (fun n => (a n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha, Filter.Eventually.of_forall fun n => (a n).2⟩
  have hLap := tendsto_laplace_integral_zero r hr hint
  have hA : Tendsto (fun n => inner ℝ f (transitionResolvent hP (a n) f)) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), r t)) := by
    have h := hLap.comp ha'
    simp only [Function.comp_def] at h
    simp_rw [inner_transitionResolvent hP _ f f]
    exact h
  have hB : Tendsto (fun n => inner ℝ f (transitionResolvent hP (b n) f)) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), r t)) := by
    have h := hLap.comp hb'
    simp only [Function.comp_def] at h
    simp_rw [inner_transitionResolvent hP _ f f]
    exact h
  have hupper : Tendsto (fun n => 2 * (inner ℝ f (transitionResolvent hP (a n) f) -
      inner ℝ f (transitionResolvent hP (b n) f))) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using (hA.sub hB).const_mul 2
  apply squeeze_zero (g := fun n => 2 * (inner ℝ f (transitionResolvent hP (a n) f) -
      inner ℝ f (transitionResolvent hP (b n) f)))
  · intro n
    exact mul_nonneg (b n).2.le (sq_nonneg _)
  · intro n
    have hab : (a n : ℝ) ≤ b n := by
      change (b n : ℝ) / 2 ≤ b n
      have hbpos : 0 < (b n : ℝ) := (b n).2
      linarith
    have h := mul_norm_transitionResolvent_sq_le_sub hP (a n) (b n) hab f
    change ((b n : ℝ) - (b n : ℝ) / 2) * ‖transitionResolvent hP (b n) f‖ ^ 2 ≤ _ at h
    nlinarith
  · exact hupper

end EinsteinFull.External.DFGW
