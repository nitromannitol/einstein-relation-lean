import EinsteinRelation.Correctors.ConditionalSpatialMollifierMoment

/-! # Joint moments of moving conditional versions

Source: `paper/main.tex:921–925,942–947`. The common moving version is
jointly MemLp whenever the reflected source is jointly MemLp. This permits
finite sums inside the literal derivative integrals almost surely.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
open scoped ENNReal
namespace EinsteinRelation.Correctors

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- The moving conditional average contracts a spatially integrated source
moment. Source: `paper/main.tex:921–925,942–947`. -/
theorem memLp_centered_conditionalSpatialAverage_product
    {d : ℕ} {L r₀ R : ℝ} (Q : EnvironmentLaw d L r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (u : FieldPair d → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hu : MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
      ((reducedEnvironmentLaw Q).prod ν)) :
    MemLp (fun z : FieldPair d × Vec d => conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) u (translate z.2 z.1) (-z.2)) p
      ((reducedEnvironmentLaw Q).prod ν) ∧
      eLpNorm (fun z : FieldPair d × Vec d => conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) u (translate z.2 z.1) (-z.2)) p
        ((reducedEnvironmentLaw Q).prod ν) ≤
        eLpNorm (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
          ((reducedEnvironmentLaw Q).prod ν) := by
  let m := reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R}
  letI : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hm : m ≤ borel (FieldPair d) := by
    dsimp only [m]
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : {x : Vec d | euclideanNorm x < 32 * R} =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hid : @Measurable (FieldPair d × Vec d) (FieldPair d × Vec d)
      ((borel (FieldPair d)).prod inferInstance) (m.prod inferInstance) id :=
    ((measurable_id'' hm).comp measurable_fst).prodMk measurable_snd
  have hcv : StronglyMeasurable
      (Function.uncurry (conditionalSpatialAverage m (reducedEnvironmentLaw Q) u)) :=
    (stronglyMeasurable_conditionalSpatialAverage m (reducedEnvironmentLaw Q) u hum).comp_measurable hid
  have hneg : Measurable (fun z : FieldPair d × Vec d => (z.1, -z.2)) :=
    measurable_fst.prodMk measurable_snd.neg
  have hv : StronglyMeasurable (fun z : FieldPair d × Vec d =>
      conditionalSpatialAverage m (reducedEnvironmentLaw Q) u z.1 (-z.2)) :=
    hcv.comp_measurable hneg
  have htranslate : MeasurePreserving
      (fun z : FieldPair d × Vec d => (translate z.2 z.1, z.2))
      ((reducedEnvironmentLaw Q).prod ν) ((reducedEnvironmentLaw Q).prod ν) :=
    Measure.measurePreserving_swap.comp
      ((measurePreserving_centerTranslate ν (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q)).comp Measure.measurePreserving_swap)
  have hmoving := hv.comp_measurable htranslate.measurable
  have hnorm := eLpNorm_comp_measurePreserving (p := p) hv.aestronglyMeasurable htranslate
  have hcond := eLpNorm_conditionalSpatialAverage_product_le m (reducedEnvironmentLaw Q)
    hm ν hp hpt (fun ω y => u ω (-y)) (hum.comp_measurable hneg) hu
  have hb := hnorm.le.trans hcond
  exact ⟨⟨hmoving.aestronglyMeasurable, hb.trans_lt hu.eLpNorm_lt_top⟩, hb⟩


end EinsteinRelation.Correctors
