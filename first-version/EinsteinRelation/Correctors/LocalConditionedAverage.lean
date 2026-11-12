import EinsteinRelation.Correctors.LocalAverageCancellation
import EinsteinRelation.Correctors.LocalConditioningBounds

/-! # Averaging the centered local conditional correctors

Source: `paper/main.tex:953–963`. This combines the comparisons on the actual
coefficient balls with cancellation of a common conditional mean. The local
conditional fields must be jointly measurable; constructing those versions and
proving their spatial weak equations are separate obligations.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- The dimension-two cancellation estimate for the local conditional fields.
The index type consists of centers in the radius-`R` ball, as imposed by the
support of `∇ζ_R`. Here `f` is the centered corrector at the origin and `g y`
is its change of mollifier normalization. Source: `paper/main.tex:953–963`.
The constant `2 * A + B` uses the conditional error at `B_{8R}` and the shifted
mean bound, without assuming a moment bound on the common conditional mean. -/
theorem local_center_conditioned_cancellation_bound {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [StandardBorelSpace E]
    {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A B : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : {y : Vec d // euclideanNorm y ≤ R} → ℝ)
    (hwm : Measurable w) (hwi : Integrable w ν) (hw : (∫ y, w y ∂ν) = 0)
    (f : FieldPair d → E) (hf : Integrable f μ)
    (g : {y : Vec d // euclideanNorm y ≤ R} → FieldPair d → E)
    (hgi : ∀ y, Integrable (g y) μ)
    (hshift : ∀ y, eLpNorm (g y) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B)
    (htail : eLpNorm (f - μ[f | reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm (z - 0) < 8 * R}]) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal A)
    (u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → E)
    (hu : Measurable u)
    (hversion : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      (fun ω => u (y, ω)) =ᵐ[μ]
        μ[f + g y | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}]) :
    (∀ᵐ ω ∂μ, Integrable (fun y => w y • u (y, ω)) ν) ∧
      MemLp (fun ω => ∫ y, w y • u (y, ω) ∂ν) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun ω => ∫ y, w y • u (y, ω) ∂ν) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal ((2 * A + B) * ∫ y, |w y| ∂ν) := by
  let U : Set (Vec d) := {z | euclideanNorm (z - 0) < 16 * R}
  let c : FieldPair d → E := μ[f | reducedCoefficientObservationSigma U]
  have heval : Measurable (fun (ω : FieldPair d) (x : U) => ω.1 x) :=
    measurable_pi_lambda _ fun x =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable
  have hobs : reducedCoefficientObservationSigma U ≤
      (inferInstance : MeasurableSpace (FieldPair d)) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact heval.comap_le
  have hc : Measurable c := (stronglyMeasurable_condExp.mono hobs).measurable
  apply local_average_cancellation_bound μ ν hp (by positivity) w hwm hwi hw
    u hu c hc
  intro y
  have hbound : eLpNorm (fun ω => u (y, ω) - c ω) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2 * A + B) := by
    have hceq : (fun ω => u (y, ω) - c ω) =ᵐ[μ]
        μ[f + g y | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] - c := by
      filter_upwards [hversion y] with ω hω
      simpa only [Pi.sub_apply] using congrArg (fun v => v - c ω) hω
    rw [eLpNorm_congr_ae hceq]
    calc
      _ ≤ 2 * eLpNorm (f - μ[f | reducedCoefficientObservationSigma
            {z : Vec d | euclideanNorm (z - 0) < 8 * R}]) (ENNReal.ofReal p) μ +
          eLpNorm (g y) (ENNReal.ofReal p) μ :=
        eLpNorm_corrector_local_centered_le hR y.2
          (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top hf (hgi y)
      _ ≤ 2 * ENNReal.ofReal A + ENNReal.ofReal B :=
        add_le_add (mul_le_mul_right htail 2) (hshift y)
      _ = ENNReal.ofReal (2 * A + B) := by
        rw [ENNReal.ofReal_add (by positivity) hB, ENNReal.ofReal_mul (by norm_num)]
        norm_num
  exact ⟨⟨((hu.comp (measurable_const.prodMk measurable_id)).sub hc).aestronglyMeasurable,
    hbound.trans_lt ENNReal.ofReal_lt_top⟩, hbound⟩

end EinsteinRelation.Correctors
