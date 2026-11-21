import EinsteinFull.External.DFGW.VelocityL2
import EinsteinFull.External.DFGW.ResolventEnergyBound

/-! # Closure of generator-energy bounds

A generator-energy estimate passes to graph limits of generator-domain vectors.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A generator-energy estimate extends along a graph-convergent sequence. -/
theorem generator_energy_bound_of_tendsto (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (v : Lp ℝ 2 μ) (C : ℝ) (F : (transitionSemigroup hP).generatorDomain)
    (Fseq : ℕ → (transitionSemigroup hP).generatorDomain)
    (hF : Tendsto (fun n => (Fseq n : Lp ℝ 2 μ)) atTop (𝓝 (F : Lp ℝ 2 μ)))
    (hgen : Tendsto (fun n => (transitionSemigroup hP).generator (Fseq n)) atTop
      (𝓝 ((transitionSemigroup hP).generator F)))
    (hbound : ∀ n, (inner ℝ v (Fseq n : Lp ℝ 2 μ)) ^ 2 ≤
      C * (-inner ℝ (Fseq n : Lp ℝ 2 μ) ((transitionSemigroup hP).generator (Fseq n)))) :
    (inner ℝ v (F : Lp ℝ 2 μ)) ^ 2 ≤
      C * (-inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F)) := by
  have hl := (Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v)) hF).pow 2
  have hr := ((Filter.Tendsto.inner (𝕜 := ℝ) hF hgen).neg).const_mul C
  exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hbound)

end EinsteinFull.External.DFGW
