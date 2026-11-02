import EinsteinFull.Calculus.S2ReducedLawUniquenessSupport
import Mathlib.Probability.Kernel.Composition.Prod
import EinsteinRelation.Localization.CoefficientObservations
import EinsteinFull.Calculus.S2QuenchedExtension
import EinsteinFull.Calculus.S2UnforcedSemigroupSupport

/-! Actual environment marginals of a normalized origin path kernel.
Normalization changes only a null set of physical environments. These results
construct no invariant law and assert no horizontal generator identification. -/

open MeasureTheory ProbabilityTheory BoundedContinuousFunction
open scoped NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The literal environment seen at one time, retaining the original reduction. -/
def c2EnvironmentAt {d : ℕ} (t : ℝ≥0) (p : FieldPair d × Path d) : FieldPair d :=
  translate (p.2 t) (reduce p.1)

theorem measurable_c2EnvironmentAt {d : ℕ} (t : ℝ≥0) :
    Measurable (c2EnvironmentAt (d := d) t) :=
  Probability.continuous_translate.measurable.comp
    (((measurable_pathPosition t).comp measurable_snd).prodMk
      (Probability.measurable_reduce.comp measurable_fst))

/-- The actual environment marginal of a Markov origin kernel. -/
def c2EnvironmentKernel {d : ℕ} (K : Kernel (FieldPair d) (Path d))
    (t : ℝ≥0) : Kernel (FieldPair d) (FieldPair d) :=
  (Kernel.prod Kernel.id K).map (c2EnvironmentAt t)

instance {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K] (t : ℝ≥0) :
    IsMarkovKernel (c2EnvironmentKernel K t) := by
  unfold c2EnvironmentKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_c2EnvironmentAt t)

/-- Its measure is exactly the literal pushforward, including on exceptional environments. -/
theorem c2EnvironmentKernel_apply {d : ℕ} (K : Kernel (FieldPair d) (Path d))
    [IsMarkovKernel K] (t : ℝ≥0) (ω : FieldPair d) :
    c2EnvironmentKernel K t ω =
      (K ω).map (fun γ => translate (γ t) (reduce ω)) := by
  have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) :=
    (measurable_c2EnvironmentAt t).comp
      (measurable_const.prodMk measurable_id)
  ext s hs
  rw [c2EnvironmentKernel, Kernel.map_apply _ (measurable_c2EnvironmentAt t),
    Measure.map_apply (measurable_c2EnvironmentAt t) hs,
    Kernel.id_prod_apply' K ω (hs.preimage (measurable_c2EnvironmentAt t)),
    Measure.map_apply hm hs]
  rfl

/-- Extract an actual probability kernel from `hpath`; every other reduced MP
solution has the same origin law a.e. This does not require smooth environments. -/
theorem exists_c2UnforcedOriginKernel
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q) (i : Fin d) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (K ω)) ∧
      ∀ Y : QuenchedPathLaws d,
        (∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω))) →
        ∀ᵐ ω ∂Q.measure, K ω = Y (0, ω) := by
  obtain ⟨⟨_PX, Y0, _hPX, hY0⟩, _⟩ := hpath i 0
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y0 ω) :=
    hY0.mono fun _ h => h.1
  obtain ⟨K, hK, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  refine ⟨K, hmarkov, ?_, ?_⟩
  · filter_upwards [hK, hY0] with ω he hω
    rw [← he]
    exact hω
  · intro Y hY
    have hu := reducedOriginLaw_ae_unique_of_pathwise (hpath := hpath) Q i 0 Y0 Y hY0 hY
    filter_upwards [hK, hu] with ω he hu
    exact he.symm.trans hu

/-- The analytic bridge only needs bounded continuous tests on the constructed
marginal kernel: the existing domination/density argument supplies integrability
and identification for every actual complex L2 representative. This is a
conditional support result, not a producer of the bounded-test identity. -/
theorem c2Unforced_path_identity_of_bounded_tests
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hid : ∀ (t : ℝ≥0) (g : FieldPair d →ᵇ ℂ) (F : Lp ℂ 2 (reducedLaw Q)),
      F =ᵐ[reducedLaw Q] (fun ω => g ω) →
      (fun ω => forcedComplexEvolution Q i 0 t F (reduce ω)) =ᵐ[Q.measure]
        fun ω => ∫ η, g η ∂c2EnvironmentKernel K t ω)
    (t : ℝ≥0) (F : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => F (translate (γ t) (reduce ω))) (K ω) ∧
      forcedComplexEvolution Q i 0 t F (reduce ω) =
        ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂K ω := by
  have : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  have : PolishSpace (FieldPair d) := inferInstance
  have hn : ‖forcedComplexEvolution Q i 0 t‖ ≤ (1 : ℝ≥0) :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun f => by
      simpa only [NNReal.coe_one, one_mul] using
        norm_forcedComplexEvolution_zero_apply_le Q i t f
  have h := quenched_apply_eq_integral Q.measure reduce Probability.measurable_reduce
    (c2EnvironmentKernel K t) (forcedComplexEvolution Q i 0 t) 1 hn (hid t) F
  filter_upwards [h] with ω hω
  rw [c2EnvironmentKernel_apply] at hω
  have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) :=
    (measurable_c2EnvironmentAt t).comp (measurable_const.prodMk measurable_id)
  refine ⟨hω.1.comp_aemeasurable hm.aemeasurable, ?_⟩
  exact hω.2.trans (integral_map hm.aemeasurable
    (Lp.stronglyMeasurable F).aestronglyMeasurable)

end EinsteinFull
