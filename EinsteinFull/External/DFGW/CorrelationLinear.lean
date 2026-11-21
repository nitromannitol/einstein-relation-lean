import EinsteinFull.External.DFGW.Correlation

/-! # Linear combinations of integrable autocorrelations

The vectors with integrable semigroup autocorrelation are closed under finite linear
combinations.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Integrable autocorrelations are stable under addition. -/
theorem integrableOn_autocorrelation_add (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : Lp ℝ 2 μ)
    (hf : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f)) (Set.Ioi 0))
    (hg : IntegrableOn (fun t : ℝ => inner ℝ g (transitionOperator hP t.toNNReal g)) (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ => inner ℝ (f + g) (transitionOperator hP t.toNNReal (f + g)))
      (Set.Ioi 0) := by
  have hfg := integrableOn_mixed_correlation hP f g hf hg
  have hgf := integrableOn_mixed_correlation hP g f hg hf
  have h := (hf.add hfg).add (hgf.add hg)
  apply h.congr
  filter_upwards with t
  simp only [Pi.add_apply, map_add, inner_add_left, inner_add_right]
  ring

/-- Integrable autocorrelations are stable under scalar multiplication. -/
theorem integrableOn_autocorrelation_smul (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (a : ℝ)
    (hf : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f)) (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ => inner ℝ (a • f) (transitionOperator hP t.toNNReal (a • f)))
      (Set.Ioi 0) := by
  have h := hf.const_mul (a ^ 2)
  apply h.congr
  filter_upwards with t
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

end EinsteinFull.External.DFGW
