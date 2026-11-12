import EinsteinRelation.External.GMPLocalityInput
import EinsteinRelation.Probability.ContinuousFieldDecoder
import Mathlib.Topology.Metrizable.ContinuousMap

/-! # Uniqueness of the GMP path law from locality

The locality input used in `paper/main.tex:381–387` applies in particular to the whole
space. There the stopped path is the original path. Decoding continuous paths from their
evaluations transfers the resulting equality of raw path laws back to `Path d`.
-/

open MeasureTheory
open scoped NNReal ENNReal
open EinsteinRelation.External.GantertSection7Support

namespace EinsteinRelation.Diffusion

/-- The cited locality input implies uniqueness of the fixed-environment path law.
This supplies the law identification used in `paper/main.tex:445–517`. -/
theorem realization_pathLaw_eq_of_locality (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1) :
    r.pathLaw = r'.pathLaw := by
  obtain ⟨D, hD, hdecode⟩ :=
    Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0) (E := Vec d)
  have hraw : Measurable (fun γ : Path d => fun t : ℝ≥0 => γ t) :=
    measurable_pi_lambda _ fun t => (continuous_eval_const t).measurable
  apply ProbabilityTheory.Kernel.ext
  intro x
  have hstop := hLoc d hd Λ₀ hΛ₀ Set.univ isOpen_univ ω ω hω hω lam h0 h1
    (fun _ _ => ⟨rfl, rfl⟩) r r' x (Set.mem_univ x)
    (fun γ t => γ t) (by intro γ t; simp)
  have heq := congrArg (Measure.map D) hstop.2
  simpa only [Measure.map_map hD hraw, Function.comp_def, hdecode,
    Measure.map_id'] using heq


end EinsteinRelation.Diffusion
