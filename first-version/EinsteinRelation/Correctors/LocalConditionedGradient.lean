import EinsteinRelation.Correctors.LocalAverageError
import EinsteinRelation.Correctors.LocalGradientEuclideanLp

/-! # Error of the averaged local conditional gradient

Source: `paper/main.tex:968–973`. The centers lie in `B_R`, the conditional
fields observe `B_{32R}(y)`, and their average has the error controlled by
the conditional error at `B_{8R}`. Jointly measurable conditional versions
are supplied explicitly; no continuity or uniqueness is assumed here.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Averaging the actual local conditional versions preserves the factor-two
nested-ball error bound. Source: `paper/main.tex:968–973`. -/
theorem local_center_conditioned_gradient_bound {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [StandardBorelSpace E]
    {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (w : {y : Vec d // euclideanNorm y ≤ R} → ℝ)
    (hwm : Measurable w) (hwi : Integrable w ν) (hw0 : ∀ y, 0 ≤ w y)
    (hw : (∫ y, w y ∂ν) = 1)
    (f : FieldPair d → E) (hf : Integrable f μ) (hfm : Measurable f)
    (htail : eLpNorm (f - μ[f | reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm (z - 0) < 8 * R}]) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal A)
    (u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → E)
    (hu : Measurable u)
    (hversion : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      (fun ω => u (y, ω)) =ᵐ[μ]
        μ[f | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}]) :
    (∀ᵐ ω ∂μ, Integrable (fun y => w y • u (y, ω)) ν) ∧
      MemLp (fun ω => (∫ y, w y • u (y, ω) ∂ν) - f ω) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => (∫ y, w y • u (y, ω) ∂ν) - f ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * A) := by
  have hfluct : ∀ y, MemLp (fun ω => u (y, ω) - f ω) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => u (y, ω) - f ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * A) := by
    intro y
    have heq : (fun ω => u (y, ω) - f ω) =ᵐ[μ]
        μ[f | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] - f := by
      filter_upwards [hversion y] with ω hω
      exact congrArg (fun v => v - f ω) hω
    have hb : eLpNorm (fun ω => u (y, ω) - f ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * A) := by
      rw [eLpNorm_congr_ae heq]
      calc
        _ ≤ 2 * eLpNorm (f - μ[f | reducedCoefficientObservationSigma
            {z : Vec d | euclideanNorm (z - 0) < 8 * R}]) (ENNReal.ofReal p) μ :=
          eLpNorm_corrector_local_gradient_error_le hR y.2
            (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top hf
        _ ≤ 2 * ENNReal.ofReal A := mul_le_mul_right htail 2
        _ = ENNReal.ofReal (2 * A) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
    exact ⟨⟨((hu.comp (measurable_const.prodMk measurable_id)).sub hfm).aestronglyMeasurable,
      hb.trans_lt ENNReal.ofReal_lt_top⟩, hb⟩
  have havg := local_average_error_bound μ ν hp (by positivity) w hwm hwi hw u hu f hfm
    hfluct
  have hwabs : (∫ y, |w y| ∂ν) = 1 := by
    simpa only [abs_of_nonneg (hw0 _)] using hw
  simpa only [hwabs, mul_one] using havg

/-- The averaged conditional gradient estimate in the paper's literal
Euclidean norm on coordinate vectors. Source: `paper/main.tex:968–973`.
The conditional expectations are of the original coordinate-valued field. -/
theorem local_center_conditioned_euclidean_gradient_bound {d : ℕ}
    {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (w : {y : Vec d // euclideanNorm y ≤ R} → ℝ)
    (hwm : Measurable w) (hwi : Integrable w ν) (hw0 : ∀ y, 0 ≤ w y)
    (hw : (∫ y, w y ∂ν) = 1)
    (f : FieldPair d → Vec d) (hf : Integrable f μ) (hfm : Measurable f)
    (htail : eLpNorm (fun ω => euclideanNorm
      (f ω - μ[f | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal A)
    (u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Vec d)
    (hu : Measurable u)
    (hversion : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      (fun ω => u (y, ω)) =ᵐ[μ]
        μ[f | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}]) :
    (∀ᵐ ω ∂μ, Integrable (fun y => w y • u (y, ω)) ν) ∧
      MemLp (fun ω => euclideanNorm ((∫ y, w y • u (y, ω) ∂ν) - f ω))
        (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => euclideanNorm ((∫ y, w y • u (y, ω) ∂ν) - f ω))
        (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (2 * A) := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hfi : Integrable (fun ω => J (f ω)) μ := J.toContinuousLinearMap.integrable_comp hf
  have htailJ : eLpNorm ((fun ω => J (f ω)) -
      μ[fun ω => J (f ω) | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}]) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal A := by
    change eLpNorm ((fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin d))) -
      μ[fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin d)) |
        reducedCoefficientObservationSigma {z : Vec d | euclideanNorm (z - 0) < 8 * R}])
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal A
    rw [← eLpNorm_euclidean_sub_condExp_error_eq hf]
    exact htail
  have hversionJ : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      (fun ω => J (u (y, ω))) =ᵐ[μ]
        μ[fun ω => J (f ω) | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] := by
    intro y
    filter_upwards [hversion y, ae_toLp_condExp hf
      (m := reducedCoefficientObservationSigma
        {x : Vec d | euclideanNorm (x - y.1) < 32 * R})] with ω hω hJω
    exact (congrArg J hω).trans hJω
  obtain ⟨hsec, hmem, hb⟩ := local_center_conditioned_gradient_bound hR ν hp hA
    w hwm hwi hw0 hw (fun ω => J (f ω)) hfi (J.continuous.measurable.comp hfm)
    htailJ (fun z => J (u z)) (J.continuous.measurable.comp hu) hversionJ
  have heq : (fun ω => euclideanNorm ((∫ y, w y • u (y, ω) ∂ν) - f ω)) =
      (fun ω => ‖(∫ y, w y • J (u (y, ω)) ∂ν) - J (f ω)‖) := by
    funext ω
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    congr 1
    change J ((∫ y, w y • u (y, ω) ∂ν) - f ω) = _
    rw [map_sub, ← J.integral_comp_comm]
    simp only [map_smul]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hsec] with ω hω
    have hi := J.symm.toContinuousLinearMap.integrable_comp hω
    simpa only [Function.comp_def, map_smul,
      ContinuousLinearEquiv.symm_apply_apply] using hi
  · rw [heq]
    exact hmem.norm
  · rw [heq, eLpNorm_norm]
    exact hb

end EinsteinRelation.Correctors
