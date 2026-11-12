import EinsteinRelation.Correctors.LocalConditionedAverage
import EinsteinRelation.Correctors.LocalGradientEuclideanLp

/-! # Vector-valued Euclidean cancellation of the local conditional mean

Source: `paper/main.tex:953–963`. The general cancellation estimate of the
local conditional correctors holds for vector fields measured in the
manuscript's Euclidean norm: the same conditional sigma algebras, the exact
conditional versions, and the literal Bochner integral of the weighted field,
with the constant `2 * A + B` and no additional probabilistic hypothesis.
This is an internal transport of the generic value-space theorem to `Vec n`
through the Euclidean identification, used for the vector-valued
weight-derivative term of Proposition 5.3.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- The vector-valued Euclidean form of the dimension-two cancellation
estimate for the local conditional fields. The value type is `Vec n`, the
hypotheses use the manuscript's Euclidean norm of the original coordinate
errors, and the conclusion controls the Euclidean norm of the literal
weighted vector integral by `(2 * A + B) * ∫ |w|`. Source:
`paper/main.tex:953–963`. -/
theorem local_center_conditioned_euclidean_cancellation_bound {d n : ℕ}
    {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A B : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : {y : Vec d // euclideanNorm y ≤ R} → ℝ)
    (hwm : Measurable w) (hwi : Integrable w ν) (hw : (∫ y, w y ∂ν) = 0)
    (f : FieldPair d → Vec n) (hf : Integrable f μ)
    (g : {y : Vec d // euclideanNorm y ≤ R} → FieldPair d → Vec n)
    (hgi : ∀ y, Integrable (g y) μ)
    (hshift : ∀ y, eLpNorm (fun ω => euclideanNorm (g y ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal B)
    (htail : eLpNorm (fun ω => euclideanNorm (f ω - μ[f | reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal A)
    (u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Vec n)
    (hu : Measurable u)
    (hversion : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      (fun ω => u (y, ω)) =ᵐ[μ]
        μ[f + g y | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}]) :
    (∀ᵐ ω ∂μ, Integrable (fun y => w y • u (y, ω)) ν) ∧
      MemLp (fun ω => euclideanNorm (∫ y, w y • u (y, ω) ∂ν)) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => euclideanNorm (∫ y, w y • u (y, ω) ∂ν)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal ((2 * A + B) * ∫ y, |w y| ∂ν) := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have hFi : Integrable (fun ω => J (f ω)) μ := J.toContinuousLinearMap.integrable_comp hf
  have hGi : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      Integrable (fun ω => J (g y ω)) μ :=
    fun y => J.toContinuousLinearMap.integrable_comp (hgi y)
  have hshiftJ : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      eLpNorm (fun ω => J (g y ω)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B := by
    intro y
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp, eLpNorm_norm] using hshift y
  have htailJ : eLpNorm ((fun ω => J (f ω)) -
      μ[fun ω => J (f ω) | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}]) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal A := by
    change eLpNorm ((fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin n))) -
      μ[fun ω => (WithLp.toLp 2 (f ω) : EuclideanSpace ℝ (Fin n)) |
        reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}]) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal A
    rw [← eLpNorm_euclidean_sub_condExp_error_eq hf]
    exact htail
  have hsplit : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      μ[(fun ω => J (f ω)) + (fun ω => J (g y ω)) | reducedCoefficientObservationSigma
        {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] =
        μ[fun ω => J ((f + g y) ω) | reducedCoefficientObservationSigma
        {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] := by
    intro y
    refine congrArg (fun h => μ[h | reducedCoefficientObservationSigma
      {x : Vec d | euclideanNorm (x - y.1) < 32 * R}]) ?_
    funext ω
    simp only [Pi.add_apply, map_add]
  have hversionJ : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      (fun ω => J (u (y, ω))) =ᵐ[μ]
        μ[(fun ω => J (f ω)) + (fun ω => J (g y ω)) | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] := by
    intro y
    filter_upwards [hversion y, ae_toLp_condExp (hf.add (hgi y))
      (m := reducedCoefficientObservationSigma
        {x : Vec d | euclideanNorm (x - y.1) < 32 * R})] with ω hω hJω
    rw [hsplit y]
    exact (congrArg J hω).trans hJω
  obtain ⟨hsec, hmem, hb⟩ := local_center_conditioned_cancellation_bound hR ν hp hA hB
    w hwm hwi hw (fun ω => J (f ω)) hFi
    (fun (y : {y : Vec d // euclideanNorm y ≤ R}) (ω : FieldPair d) => J (g y ω)) hGi
    hshiftJ htailJ (fun z => J (u z)) (J.continuous.measurable.comp hu) hversionJ
  have heq : (fun ω => euclideanNorm (∫ y, w y • u (y, ω) ∂ν)) =
      (fun ω => ‖∫ y, w y • J (u (y, ω)) ∂ν‖) := by
    funext ω
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    congr 1
    change J (∫ y, w y • u (y, ω) ∂ν) = _
    rw [← J.integral_comp_comm]
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
