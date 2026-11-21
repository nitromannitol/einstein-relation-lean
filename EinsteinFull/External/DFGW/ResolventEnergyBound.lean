import EinsteinFull.External.DFGW.Resolvent
import EinsteinFull.External.DFGW.GeneratorEnergy

/-! # Resolvent bound from a generator-energy estimate

A generator-energy bound on a vector implies a uniform bound on its resolvent quadratic form.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- An energy estimate on the generator domain bounds the resolvent quadratic form. -/
theorem inner_transitionResolvent_le_of_energy_bound
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (v : Lp ℝ 2 μ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f : (transitionSemigroup hP).generatorDomain,
      (inner ℝ v (f : Lp ℝ 2 μ)) ^ 2 ≤
        C * (-inner ℝ (f : Lp ℝ 2 μ) ((transitionSemigroup hP).generator f)))
    (lam : MarkovProcess.Semigroup.PositiveShift) :
    inner ℝ v (transitionResolvent hP lam v) ≤ C := by
  let R := transitionResolvent hP lam v
  have hR : R ∈ (transitionSemigroup hP).generatorDomain :=
    (transitionSemigroup hP).resolvent_mem_generatorDomain lam v
  have hgen : (transitionSemigroup hP).generator ⟨R, hR⟩ = (lam : ℝ) • R - v :=
    (transitionSemigroup hP).generator_resolvent lam v
  have hb := hbound ⟨R, hR⟩
  rw [hgen, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hb
  change (inner ℝ v R) ^ 2 ≤ C * (-((lam : ℝ) * ‖R‖ ^ 2 - inner ℝ R v)) at hb
  have he : inner ℝ R v = inner ℝ v R := (real_inner_comm R v).symm
  conv at hb => rhs; rw [he]
  have hnonneg : 0 ≤ inner ℝ v R := inner_transitionResolvent_nonneg hP lam v
  have hlam : 0 ≤ (lam : ℝ) := lam.2.le
  have hterm : 0 ≤ C * ((lam : ℝ) * ‖R‖ ^ 2) := by positivity
  by_cases hz : inner ℝ v R = 0
  · rw [hz]
    exact hC
  · have hp : 0 < inner ℝ v R := lt_of_le_of_ne hnonneg (Ne.symm hz)
    nlinarith

end EinsteinFull.External.DFGW
