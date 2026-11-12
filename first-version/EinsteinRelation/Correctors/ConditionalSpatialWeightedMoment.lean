import EinsteinRelation.Correctors.ConditionalSpatialMollifierMoment

/-! # Weighted conditional averages from spatial moments

Source: `paper/main.tex:921–925,942–947`. A bounded spatial weight can be
included before conditioning. Its moving average is controlled by the
ordinary product-space source norm, without pointwise section hypotheses.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
namespace EinsteinRelation.Correctors

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- Bounded weights multiply the source norm in the common moving conditional
average. Source: `paper/main.tex:921–925,942–947`. -/
theorem eLpNorm_integral_weight_centered_conditionalSpatialAverage_le
    {d : ℕ} {L r₀ R W : ℝ} (Q : EnvironmentLaw d L r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (w : Vec d → ℝ) (hwm : Measurable w) (hW : ∀ᵐ y ∂ν, |w y| ≤ W)
    (u : FieldPair d → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hu : MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
      ((reducedEnvironmentLaw Q).prod ν)) :
    eLpNorm (fun ω => ∫ y, w y * conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) u (translate y ω) (-y) ∂ν) p
      (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal W * eLpNorm (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
        ((reducedEnvironmentLaw Q).prod ν) := by
  let v : FieldPair d → Vec d → ℝ := fun ω x => w (-x) * u ω x
  have hvm : StronglyMeasurable (Function.uncurry v) :=
    ((hwm.comp measurable_snd.neg).stronglyMeasurable).mul hum
  have hmneg : Measurable (fun z : FieldPair d × Vec d => (z.1, -z.2)) :=
    measurable_fst.prodMk measurable_snd.neg
  have hb : ∀ᵐ z ∂(reducedEnvironmentLaw Q).prod ν,
      ‖v z.1 (-z.2)‖ ≤ W * ‖u z.1 (-z.2)‖ := by
    filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hW] with z hz
    simpa only [v, neg_neg, norm_mul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hz (abs_nonneg (u z.1 (-z.2)))
  have hv : MemLp (fun z : FieldPair d × Vec d => v z.1 (-z.2)) p
      ((reducedEnvironmentLaw Q).prod ν) :=
    hu.of_le_mul (hvm.comp_measurable hmneg).aestronglyMeasurable hb
  have h := eLpNorm_integral_centered_conditionalSpatialAverage_le (R := R)
    Q ν hp hpt v hvm hv
  have heq (ω : FieldPair d) (y : Vec d) :
      conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) v (translate y ω) (-y) =
      w y * conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) u (translate y ω) (-y) := by
    simp only [conditionalSpatialAverage, v, neg_neg, integral_const_mul]
  simp only [heq] at h
  exact h.trans (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hb p)

end EinsteinRelation.Correctors
