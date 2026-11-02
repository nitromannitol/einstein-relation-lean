import EinsteinFull.Calculus.C2UnforcedProcessSupport
import EinsteinRelation.Environment.ReductionEmbedding
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! Transport of the actual environment marginal to the reduced carrier.
The measurable extension away from the joint reduction image is auxiliary.
All physical interpretations below are on that image or reduced-law a.e.;
no subinvariance or transition-semigroup identification is asserted. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Auxiliary endokernel obtained by reconstructing the physical input.
Only a left inverse on the actual reduction image is needed. -/
def c2ReducedEnvironmentKernel {d : ℕ} (K : Kernel (FieldPair d) (Path d))
    (D : FieldPair d → FieldPair d) (hD : Measurable D) (t : ℝ≥0) :
    Kernel (FieldPair d) (FieldPair d) :=
  (c2EnvironmentKernel K t).comap D hD

instance {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (D : FieldPair d → FieldPair d) (hD : Measurable D) (t : ℝ≥0) :
    IsMarkovKernel (c2ReducedEnvironmentKernel K D hD t) := by
  unfold c2ReducedEnvironmentKernel
  infer_instance

/-- Exact agreement at every actual reduced environment. -/
theorem c2ReducedEnvironmentKernel_pullback {d : ℕ}
    (K : Kernel (FieldPair d) (Path d)) (D : FieldPair d → FieldPair d)
    (hD : Measurable D) (hleft : Function.LeftInverse D reduce)
    (t : ℝ≥0) (ω : FieldPair d) :
    c2ReducedEnvironmentKernel K D hD t (reduce ω) = c2EnvironmentKernel K t ω := by
  change c2EnvironmentKernel K t (D (reduce ω)) = _
  rw [hleft ω]

/-- Consequently the annealed laws are literally the same measure. -/
theorem c2ReducedEnvironmentKernel_comp {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Kernel (FieldPair d) (Path d))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) (t : ℝ≥0) :
    c2ReducedEnvironmentKernel K D hD t ∘ₘ reducedLaw Q =
      c2EnvironmentKernel K t ∘ₘ Q.measure := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  change (∫⁻ ρ, c2ReducedEnvironmentKernel K D hD t ρ s
    ∂Q.measure.map reduce) = _
  rw [lintegral_map ((c2ReducedEnvironmentKernel K D hD t).measurable_coe hs)
    Probability.measurable_reduce]
  simp only [c2ReducedEnvironmentKernel_pullback K D hD hleft]

/-- Integral pullback needs no additional test regularity: the measures agree. -/
theorem c2ReducedEnvironmentKernel_integral {d : ℕ}
    (K : Kernel (FieldPair d) (Path d)) (D : FieldPair d → FieldPair d)
    (hD : Measurable D) (hleft : Function.LeftInverse D reduce)
    (t : ℝ≥0) (ω : FieldPair d) (g : FieldPair d → ℂ) :
    (∫ ρ, g ρ ∂c2ReducedEnvironmentKernel K D hD t (reduce ω)) =
      ∫ ρ, g ρ ∂c2EnvironmentKernel K t ω := by
  rw [c2ReducedEnvironmentKernel_pullback K D hD hleft]

/-- The MP start law fixes the actual zero-time environment marginal. -/
theorem c2EnvironmentKernel_zero_of_start {d : ℕ}
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (ω : FieldPair d) (hstart : ∀ᵐ γ ∂K ω, γ 0 = 0) :
    c2EnvironmentKernel K 0 ω = Measure.dirac (reduce ω) := by
  rw [c2EnvironmentKernel_apply]
  calc
    (K ω).map (fun γ => translate (γ 0) (reduce ω)) =
        (K ω).map (fun _ => reduce ω) := Measure.map_congr (hstart.mono fun γ h => by
          change translate (γ 0) (reduce ω) = reduce ω
          rw [h, translate_zero])
    _ = Measure.dirac (reduce ω) := by simp only [Measure.map_const, measure_univ, one_smul]

/-- Concrete transport of the same origin kernel supplied by the pathwise node.
The MP and zero-time conclusions share one physical full event. Uniqueness is
retained for that same kernel, before quantification over all marginal times. -/
theorem exists_c2ReducedUnforcedKernel
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∃ (K : Kernel (FieldPair d) (Path d))
      (R : ℝ≥0 → Kernel (FieldPair d) (FieldPair d)),
      IsMarkovKernel K ∧ (∀ t, IsMarkovKernel (R t)) ∧
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (K ω) ∧
        R 0 (reduce ω) = Measure.dirac (reduce ω)) ∧
      (∀ (t : ℝ≥0) (ω : FieldPair d), R t (reduce ω) = c2EnvironmentKernel K t ω) ∧
      (∀ t, R t ∘ₘ reducedLaw Q = c2EnvironmentKernel K t ∘ₘ Q.measure) ∧
      (∀ᵐ ρ ∂reducedLaw Q, R 0 ρ = Measure.dirac ρ) ∧
      (∀ Y : QuenchedPathLaws d,
        (∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω))) →
        ∀ᵐ ω ∂Q.measure, K ω = Y (0, ω) ∧
          ∀ t : ℝ≥0, R t (reduce ω) =
            (Y (0, ω)).map (fun γ => translate (γ t) (reduce ω))) := by
  obtain ⟨K, hK, hMP, huniq⟩ := exists_c2UnforcedOriginKernel (hpath := pathwiseAt_of_pathwise hpath hd) Q i
  have := hK
  obtain ⟨D, hD, hleft⟩ := Probability.exists_measurable_leftInverse_reduce d
  let R := c2ReducedEnvironmentKernel K D hD
  have hpull := c2ReducedEnvironmentKernel_pullback K D hD hleft
  have hzero : ∀ᵐ ω ∂Q.measure, R 0 (reduce ω) = Measure.dirac (reduce ω) := by
    filter_upwards [hMP] with ω hω
    rw [hpull]
    exact c2EnvironmentKernel_zero_of_start K ω hω.2.1
  refine ⟨K, R, hK, fun _ => inferInstance, hMP.and hzero, hpull,
    c2ReducedEnvironmentKernel_comp Q K D hD hleft, ?_, ?_⟩
  · exact (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr hzero
  · intro Y hY
    filter_upwards [huniq Y hY] with ω he
    refine ⟨he, fun t => ?_⟩
    rw [hpull, c2EnvironmentKernel_apply, he]

end EinsteinFull
