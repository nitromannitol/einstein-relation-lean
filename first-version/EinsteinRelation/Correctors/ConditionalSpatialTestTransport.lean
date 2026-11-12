import EinsteinRelation.Correctors.ConditionalSpatialIntegrability
import EinsteinRelation.Correctors.StationaryCenteredSpatialIntegrability
import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.Correctors.ReducedConditionalFluxEquation

/-! # Center integrability of the actual conditional fields

Source: `paper/main.tex:913–938`. Compact spatial tests turn the local
conditional versions into globally product-integrable fields. Stationarity
then supplies joint center-space integrability for almost every environment.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- A spatial test supported inside the domain extends a product-integrable
field to the whole space after multiplication. Source: `paper/main.tex:926–938`. -/
theorem integrable_spatialTest_mul_product {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} [SFinite μ] {U : Set (Vec d)} {u : Ω → Vec d → ℝ}
    (hui : Integrable (Function.uncurry u) (μ.prod (volume.restrict U)))
    {w : Vec d → ℝ} (hw : IsSpatialTest U w) :
    Integrable (fun z : Ω × Vec d => w z.2 * u z.1 z.2) (μ.prod volume) := by
  obtain ⟨C, hC⟩ := hw.2.1.exists_bound_of_continuous hw.1.continuous
  have hi : Integrable (fun z : Ω × Vec d => w z.2 * u z.1 z.2)
      (μ.prod (volume.restrict U)) :=
    hui.bdd_mul (hw.1.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z.2)
  have hs : Function.support (fun z : Ω × Vec d => w z.2 * u z.1 z.2) ⊆
      Set.univ ×ˢ U := by
    intro z hz
    exact ⟨Set.mem_univ _, hw.2.2 (subset_tsupport w (mul_ne_zero_iff.mp hz).1)⟩
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using hi

/-- The exact conditional version, translated with its center, is integrable
jointly in center and space after multiplication by any local spatial test.
Source: `paper/main.tex:913–938`. -/
theorem ae_integrable_centered_conditional_spatialTest {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (U V : Set (Vec d)) [IsFiniteMeasure (volume.restrict V)]
    (u : FieldPair d → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hui : Integrable (Function.uncurry u)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)))
    {w : Vec d → ℝ} (hw : IsSpatialTest U w) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun z : Vec d × Vec d =>
      w (z.2 - z.1) * conditionalSpatialAverage (reducedCoefficientObservationSigma U)
        (reducedEnvironmentLaw Q) u (translate z.1 ω) (z.2 - z.1))
          (volume.prod (volume.restrict V)) := by
  have hm : reducedCoefficientObservationSigma U ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : U =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hi := integrable_conditionalSpatialAverage_product
    (reducedCoefficientObservationSigma U) (reducedEnvironmentLaw Q) hm
    (volume.restrict U) u hum hui
  have hwf := integrable_spatialTest_mul_product hi hw
  exact ae_integrable_centered_stationary_spatial_field (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (volume.restrict V) hwf.swap

end EinsteinRelation.Correctors
