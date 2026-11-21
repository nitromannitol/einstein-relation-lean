import EinsteinFull.External.DFGW.FatouIntegrability
import EinsteinFull.External.DFGW.CorrelationRepresentation

/-! # Integrability of velocity correlations

The resolvent bound and positivity of the reversible semigroup imply integrability of the
velocity autocorrelations and absolute integrability of the mixed correlations.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A uniform resolvent bound implies integrability of the nonnegative autocorrelation. -/
theorem integrableOn_autocorrelation_of_resolvent_bound
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ) (C : ℝ)
    (hbound : ∀ lam : MarkovProcess.Semigroup.PositiveShift,
      inner ℝ f (transitionResolvent hP lam f) ≤ C) :
    IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f)) (Set.Ioi 0) := by
  let A := transitionSemigroup hP
  let r : ℝ → ℝ := fun t => inner ℝ f (A t.toNNReal f)
  let lam : ℕ → MarkovProcess.Semigroup.PositiveShift := fun n =>
    ⟨1 / ((n : ℝ) + 1), by change 0 < 1 / ((n : ℝ) + 1); positivity⟩
  let g : ℕ → ℝ → ℝ := fun n t => Real.exp (-(lam n : ℝ) * t) * r t
  have hrcont : Continuous r :=
    continuous_const.inner ((A.continuous_orbit f).comp continuous_real_toNNReal)
  have hrpos : ∀ t, 0 ≤ r t := fun t => inner_transitionSemigroup_nonneg hP t.toNNReal f
  have hgint : ∀ n, IntegrableOn (g n) (Set.Ioi 0) := by
    intro n
    have h := (A.integrableOn_laplaceIntegrand (lam n).2 f).const_inner (𝕜 := ℝ) f
    simp only [A.laplaceIntegrand_apply, real_inner_smul_right] at h
    exact h
  have hgpos : ∀ n, 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] g n := by
    intro n
    exact Filter.Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (hrpos t)
  have hlim : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Tendsto (fun n => g n t) atTop (𝓝 (r t)) := by
    apply Filter.Eventually.of_forall
    intro t
    have hlam : Tendsto (fun n => (lam n : ℝ)) atTop (𝓝 0) := by
      simpa only [lam] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hz : Tendsto (fun n => -(lam n : ℝ) * t) atTop (𝓝 0) := by
      simpa only [neg_zero, zero_mul] using (hlam.neg).mul_const t
    have he := (Real.continuous_exp.tendsto 0).comp hz
    simpa only [g, Function.comp_def, neg_zero, zero_mul, Real.exp_zero, one_mul] using he.mul_const (r t)
  apply integrable_of_nonneg_tendsto_integral_bounded hrcont.aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall hrpos) hgint hgpos hlim C
  intro n
  change (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lam n : ℝ) * t) *
    inner ℝ f (transitionSemigroup hP t.toNNReal f)) ≤ C
  rw [← inner_transitionResolvent hP (lam n) f f]
  exact hbound (lam n)

end EinsteinFull.External.DFGW
