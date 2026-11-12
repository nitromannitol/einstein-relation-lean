import EinsteinRelation.Correctors.ConditionalSpatialLpContraction
import EinsteinRelation.Correctors.CanonicalConditionalCenterVersions
import EinsteinRelation.Correctors.StationaryCenterTransport

/-! # Conditional mollifier moments from spatial moments

Source: `paper/main.tex:921–925,942–947`. The actual moving conditional
averages are controlled by product-space source moments.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- The moving conditional average contracts a spatially integrated source
moment. Source: `paper/main.tex:921–925,942–947`. -/
theorem eLpNorm_integral_centered_conditionalSpatialAverage_le
    {d : ℕ} {L r₀ R : ℝ} (Q : EnvironmentLaw d L r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (u : FieldPair d → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hu : MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
      ((reducedEnvironmentLaw Q).prod ν)) :
    eLpNorm (fun ω => ∫ y, conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) u (translate y ω) (-y) ∂ν) p
      (reducedEnvironmentLaw Q) ≤
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
  have havg := eLpNorm_kernel_integral_le (μ := reducedEnvironmentLaw Q)
    (ProbabilityTheory.Kernel.const (FieldPair d) ν) hp hpt hmoving
  simp only [ProbabilityTheory.Kernel.const_apply, Measure.compProd_const] at havg
  have hnorm := eLpNorm_comp_measurePreserving (p := p) hv.aestronglyMeasurable htranslate
  have hcond := eLpNorm_conditionalSpatialAverage_product_le m (reducedEnvironmentLaw Q)
    hm ν hp hpt (fun ω y => u ω (-y)) (hum.comp_measurable hneg) hu
  exact havg.trans (hnorm.le.trans hcond)

/-- The reflected unit-mass spatial mollifier, as a measure on its centers.
Source: `paper/main.tex:921–925`. -/
def mollifierCenterMeasure (d : ℕ) (R : ℝ) : Measure (Vec d) :=
  volume.withDensity (fun y => ENNReal.ofReal (Calculus.unitMassScaledMollifier d R (-y)))

/-- The center measure has total mass one at positive radii.
Source: `paper/main.tex:921–925`. -/
theorem isProbabilityMeasure_mollifierCenterMeasure {d : ℕ} {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (mollifierCenterMeasure d R) := by
  have hc : Continuous (fun y : Vec d => Calculus.unitMassScaledMollifier d R (-y)) :=
    (Entropy.contDiff_unitMassScaledMollifier R).continuous.comp continuous_neg
  have hcs : HasCompactSupport (fun y : Vec d => Calculus.unitMassScaledMollifier d R (-y)) :=
    (Entropy.hasCompactSupport_unitMassScaledMollifier hR).comp_homeomorph (Homeomorph.neg _)
  constructor
  rw [mollifierCenterMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hcs)
      (ae_of_all _ fun y => Entropy.unitMassScaledMollifier_nonneg' hR _)]
  rw [integral_neg_eq_self, Entropy.integral_unitMassScaledMollifier' hR, ENNReal.ofReal_one]

/-- Integrating against the center measure is exactly the literal mollifier
integral, including the total-integral convention.
Source: `paper/main.tex:921–925`. -/
theorem integral_mollifierCenterMeasure {d : ℕ} {R : ℝ} (hR : 0 < R)
    (f : Vec d → ℝ) :
    (∫ y, f y ∂mollifierCenterMeasure d R) =
      ∫ y, Calculus.unitMassScaledMollifier d R (-y) * f y := by
  have hc : Measurable (fun y : Vec d => Calculus.unitMassScaledMollifier d R (-y)) :=
    (Entropy.contDiff_unitMassScaledMollifier R).continuous.measurable.comp measurable_neg
  rw [mollifierCenterMeasure, integral_withDensity_eq_integral_toReal_smul hc.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Entropy.unitMassScaledMollifier_nonneg' hR _), smul_eq_mul]

/-- The actual conditional mollifier is bounded by the product-space source
seminorm against the same mollifier. Source: `paper/main.tex:942–947`. -/
theorem eLpNorm_centered_conditional_mollifier_le_spatial_moment
    {d : ℕ} {L r₀ R : ℝ} (Q : EnvironmentLaw d L r₀) (hR : 0 < R)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (u : FieldPair d → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hu : MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
      ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R))) :
    eLpNorm (fun ω => ∫ y, Calculus.unitMassScaledMollifier d R (-y) *
        conditionalSpatialAverage
          (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
          (reducedEnvironmentLaw Q) u (translate y ω) (-y)) p (reducedEnvironmentLaw Q) ≤
      eLpNorm (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
        ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)) := by
  letI := isProbabilityMeasure_mollifierCenterMeasure (d := d) hR
  simpa only [integral_mollifierCenterMeasure hR] using
    eLpNorm_integral_centered_conditionalSpatialAverage_le (R := R)
      Q (mollifierCenterMeasure d R) hp hpt u hum hu

end EinsteinRelation.Correctors
