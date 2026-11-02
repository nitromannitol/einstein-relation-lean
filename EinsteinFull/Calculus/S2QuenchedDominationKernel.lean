import EinsteinFull.Calculus.S2AnnealedDominationOperator
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# `L²` domination of the annealed kernel law

Abstract setting of the path clause of `stationary-environment#unforced-process`: a probability space
`(Ξ, Q)`, a measurable `r : Ξ → Ω` (the reduction), a Markov kernel `κ : Ξ ⇝ Ω` (the quenched law of
the environment seen from the particle at time `t`), and an `L²(Q.map r)` operator `T` (the
semigroup at time `t`). If `T f ∘ r = ∫ f dκ` almost surely for every bounded continuous complex
`f`, then the annealed law `κ ∘ₘ Q` is dominated:
`∫ f d(κ ∘ₘ Q) ≤ ‖T‖ (∫ f² d(Q.map r))^{1/2}` for bounded continuous `f ≥ 0`, hence
`κ ∘ₘ Q ≪ Q.map r`.
-/

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull

variable {Ξ Ω : Type*} [MeasurableSpace Ξ] [TopologicalSpace Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

/-- A nonnegative bounded continuous function, viewed as a complex one. -/
def nnrealToComplex (f : Ω →ᵇ ℝ≥0) : Ω →ᵇ ℂ :=
  f.comp (fun a : ℝ≥0 => (((a : ℝ≥0) : ℝ) : ℂ)) (C := 1)
    (LipschitzWith.of_dist_le_mul fun a b => by
      simp [Complex.dist_eq, ← Complex.ofReal_sub, NNReal.dist_eq])

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] in
@[simp] theorem nnrealToComplex_apply (f : Ω →ᵇ ℝ≥0) (x : Ω) :
    nnrealToComplex f x = (((f x : ℝ≥0) : ℝ) : ℂ) := rfl

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
theorem lintegral_nnreal_eq_enorm_integral (m : Measure Ω) [IsFiniteMeasure m] (f : Ω →ᵇ ℝ≥0) :
    ∫⁻ x, (f x : ℝ≥0∞) ∂m = ‖∫ x, (((f x : ℝ≥0) : ℝ) : ℂ) ∂m‖ₑ := by
  have henorm : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ‖r‖ₑ := fun r => by
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  rw [integral_complex_ofReal, henorm,
    Real.enorm_eq_ofReal (integral_nonneg fun x => NNReal.coe_nonneg _),
    ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f m,
    ENNReal.ofReal_toReal (BoundedContinuousFunction.lintegral_lt_top_of_nnreal (μ := m) f).ne]

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω] in
/-- `L¹ ≤ L²` on a finite measure space, for an element of `L²`. -/
theorem lintegral_enorm_le_enorm_mul (ν : Measure Ω)
    (H : MeasureTheory.Lp ℂ 2 ν) :
    ∫⁻ x, ‖H x‖ₑ ∂ν ≤ ‖H‖ₑ * ν Set.univ ^ (1 / 2 : ℝ) := by
  have hH : AEStronglyMeasurable (fun x => H x) ν := MeasureTheory.Lp.aestronglyMeasurable _
  rw [← eLpNorm_one_eq_lintegral_enorm hH, MeasureTheory.Lp.enorm_def]
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hH).trans
    (le_of_eq ?_)
  norm_num

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω] in
/-- Operator bound in extended norms. -/
theorem enorm_apply_le (ν : Measure Ω) (T : MeasureTheory.Lp ℂ 2 ν →L[ℂ] MeasureTheory.Lp ℂ 2 ν)
    (M : ℝ≥0) (hT : ‖T‖ ≤ M) (F : MeasureTheory.Lp ℂ 2 ν) :
    ‖T F‖ₑ ≤ (M : ℝ≥0∞) * ‖F‖ₑ := by
  rw [← ofReal_norm (T F), ← ofReal_norm F]
  calc ENNReal.ofReal ‖T F‖ ≤ ENNReal.ofReal ((M : ℝ) * ‖F‖) :=
        ENNReal.ofReal_le_ofReal
          ((T.le_opNorm F).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _)))
    _ = (M : ℝ≥0∞) * ENNReal.ofReal ‖F‖ := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg M), ENNReal.ofReal_coe_nnreal]

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- The extended norm of an `L²` class with a bounded continuous nonnegative representative. -/
theorem enorm_eq_of_ae_eq_nnreal (ν : Measure Ω) (f : Ω →ᵇ ℝ≥0)
    (F : MeasureTheory.Lp ℂ 2 ν) (hF : F =ᵐ[ν] fun x => (((f x : ℝ≥0) : ℝ) : ℂ)) :
    ‖F‖ₑ = (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  have hfc : Continuous fun x => ((f x : ℝ≥0) : ℝ) := NNReal.continuous_coe.comp f.continuous
  have hFm : AEStronglyMeasurable (fun x => (((f x : ℝ≥0) : ℝ) : ℂ)) ν :=
    (Complex.continuous_ofReal.comp hfc).aestronglyMeasurable
  have henorm : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ‖r‖ₑ := fun r => by
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  rw [MeasureTheory.Lp.enorm_def, eLpNorm_congr_ae hF,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hFm]
  have hen : ∀ x, ‖(((f x : ℝ≥0) : ℝ) : ℂ)‖ₑ ^ ((2 : ℝ≥0∞).toReal) = (f x : ℝ≥0∞) ^ 2 := by
    intro x
    rw [henorm, Real.enorm_eq_ofReal (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
      ENNReal.toReal_ofNat, ENNReal.rpow_two]
  simp_rw [hen]
  norm_num

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- `L²` domination of the annealed kernel law on bounded continuous nonnegative tests. -/
theorem lintegral_bind_le_of_apply (Q : Measure Ξ) [IsProbabilityMeasure Q] (r : Ξ → Ω)
    (hr : Measurable r) (κ : Kernel Ξ Ω) [IsMarkovKernel κ]
    (T : MeasureTheory.Lp ℂ 2 (Q.map r) →L[ℂ] MeasureTheory.Lp ℂ 2 (Q.map r)) (M : ℝ≥0)
    (hT : ‖T‖ ≤ M)
    (hid : ∀ (f : Ω →ᵇ ℂ) (F : MeasureTheory.Lp ℂ 2 (Q.map r)),
      F =ᵐ[Q.map r] (fun x => f x) →
      (fun ω => T F (r ω)) =ᵐ[Q] fun ω => ∫ x, f x ∂κ ω)
    (f : Ω →ᵇ ℝ≥0) :
    ∫⁻ x, (f x : ℝ≥0∞) ∂(Measure.bind Q κ) ≤
      (M : ℝ≥0∞) * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂(Q.map r)) ^ (1 / 2 : ℝ) := by
  let F : MeasureTheory.Lp ℂ 2 (Q.map r) :=
    BoundedContinuousFunction.toLp 2 (Q.map r) ℂ (nnrealToComplex f)
  have hF : F =ᵐ[Q.map r] fun x => (((f x : ℝ≥0) : ℝ) : ℂ) :=
    BoundedContinuousFunction.coeFn_toLp 2 (Q.map r) ℂ (nnrealToComplex f)
  have key : ∀ᵐ ω ∂Q, ∫⁻ x, (f x : ℝ≥0∞) ∂κ ω = ‖T F (r ω)‖ₑ := by
    filter_upwards [hid (nnrealToComplex f) F hF] with ω hω
    rw [lintegral_nnreal_eq_enorm_integral, hω]
    rfl
  have hmeasf : Measurable fun x => (f x : ℝ≥0∞) :=
    ENNReal.continuous_coe.measurable.comp f.continuous.measurable
  have hTFm : Measurable fun x => ‖T F x‖ₑ :=
    (MeasureTheory.Lp.stronglyMeasurable (T F)).measurable.enorm
  calc ∫⁻ x, (f x : ℝ≥0∞) ∂(Measure.bind Q κ)
      = ∫⁻ ω, ∫⁻ x, (f x : ℝ≥0∞) ∂κ ω ∂Q :=
        Measure.lintegral_bind κ.aemeasurable hmeasf.aemeasurable
    _ = ∫⁻ ω, ‖T F (r ω)‖ₑ ∂Q := lintegral_congr_ae key
    _ = ∫⁻ x, ‖T F x‖ₑ ∂(Q.map r) := (lintegral_map hTFm hr).symm
    _ ≤ ‖T F‖ₑ * (Q.map r) Set.univ ^ (1 / 2 : ℝ) := lintegral_enorm_le_enorm_mul _ _
    _ = ‖T F‖ₑ := by
        rw [Measure.map_apply hr MeasurableSet.univ, Set.preimage_univ, measure_univ,
          ENNReal.one_rpow, mul_one]
    _ ≤ (M : ℝ≥0∞) * ‖F‖ₑ := enorm_apply_le _ T M hT F
    _ = (M : ℝ≥0∞) * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂(Q.map r)) ^ (1 / 2 : ℝ) := by
        rw [enorm_eq_of_ae_eq_nnreal _ f F hF]

/-- The annealed kernel law is absolutely continuous with respect to the reduced law. -/
theorem bind_absolutelyContinuous_of_apply (Q : Measure Ξ) [IsProbabilityMeasure Q] (r : Ξ → Ω)
    (hr : Measurable r) (κ : Kernel Ξ Ω) [IsMarkovKernel κ]
    (T : MeasureTheory.Lp ℂ 2 (Q.map r) →L[ℂ] MeasureTheory.Lp ℂ 2 (Q.map r)) (M : ℝ≥0)
    (hT : ‖T‖ ≤ M)
    (hid : ∀ (f : Ω →ᵇ ℂ) (F : MeasureTheory.Lp ℂ 2 (Q.map r)),
      F =ᵐ[Q.map r] (fun x => f x) →
      (fun ω => T F (r ω)) =ᵐ[Q] fun ω => ∫ x, f x ∂κ ω) :
    Measure.bind Q κ ≪ Q.map r := by
  haveI : IsProbabilityMeasure (Measure.bind Q κ) :=
    inferInstanceAs (IsProbabilityMeasure (κ ∘ₘ Q))
  haveI : IsProbabilityMeasure (Q.map r) := inferInstance
  exact absolutelyContinuous_of_lintegral_le_sqrt _ _ (M : ℝ≥0∞) ENNReal.coe_ne_top
    (lintegral_bind_le_of_apply Q r hr κ T M hT hid)

end EinsteinFull
