import EinsteinFull.External.DFGW.GeneratorEnergyClosure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # Approximation in the generator graph norm

Resolvents of simple functions approximate every vector in the generator domain together with
its generator. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Resolvents of simple functions form a graph-dense subset of the generator domain. -/
theorem exists_simple_resolvent_tendsto_generator (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (lam : MarkovProcess.Semigroup.PositiveShift)
    (F : (transitionSemigroup hP).generatorDomain) :
    ∃ g : ℕ → Lp.simpleFunc ℝ 2 μ,
      let G : ℕ → (transitionSemigroup hP).generatorDomain := fun n =>
        ⟨(transitionSemigroup hP).resolvent lam (g n),
          (transitionSemigroup hP).resolvent_mem_generatorDomain lam (g n)⟩
      Tendsto (fun n => (G n : Lp ℝ 2 μ)) atTop (𝓝 (F : Lp ℝ 2 μ)) ∧
      Tendsto (fun n => (transitionSemigroup hP).generator (G n)) atTop
        (𝓝 ((transitionSemigroup hP).generator F)) := by
  let A := transitionSemigroup hP
  let f : Lp ℝ 2 μ := (lam : ℝ) • (F : Lp ℝ 2 μ) - A.generator F
  have hdense := Lp.simpleFunc.denseRange (E := ℝ) (μ := μ) (p := 2) (by simp)
  obtain ⟨u, hu_mem, hu⟩ := mem_closure_iff_seq_limit.mp (hdense f)
  choose g hg using hu_mem
  have hgconv : Tendsto (fun n => (g n : Lp ℝ 2 μ)) atTop (𝓝 f) := by
    simpa only [hg] using hu
  have hres : A.resolvent lam f = (F : Lp ℝ 2 μ) := by
    exact A.resolvent_smul_sub_generator lam F
  have hF : Tendsto (fun n => A.resolvent lam (g n)) atTop (𝓝 (F : Lp ℝ 2 μ)) := by
    simpa only [Function.comp_def, hres] using
      ((A.resolvent lam).continuous.tendsto f).comp hgconv
  refine ⟨g, hF, ?_⟩
  change Tendsto (fun n => A.generator ⟨A.resolvent lam (g n),
    A.resolvent_mem_generatorDomain lam (g n)⟩) atTop (𝓝 (A.generator F))
  simp_rw [A.generator_resolvent]
  have hggen := (hF.const_smul (lam : ℝ)).sub hgconv
  have heq : (lam : ℝ) • (F : Lp ℝ 2 μ) - f = A.generator F := by
    dsimp only [f]
    abel
  simpa only [heq] using hggen

end EinsteinFull.External.DFGW
