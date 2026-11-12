import EinsteinRelation.Correctors.JointLocalConditionalOrbit

/-! # Joint conditioning of center-dependent corrector fields

Source: `paper/main.tex:913–938,948–963`. The scalar corrector and each
skew entry are centered by a mean that depends on the conditioning center.
A single conditional probability kernel constructs joint versions even
for these varying observables. Only the containing coefficient window is
observed by the resulting family.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- A jointly measurable, integrable family admits jointly local versions
of its moving-window conditional expectations. In particular, the source
observable may include a center-dependent mollified mean.
Source: `paper/main.tex:913–938,948–955`. -/
theorem exists_joint_center_conditioned_family {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (f : Vec d × FieldPair d → ℝ)
    (hf : Measurable f)
    (hfi : ∀ y, Integrable (fun ω => f (y, ω)) (reducedEnvironmentLaw Q)) :
    ∃ u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → ℝ,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) ℝ
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance u) ∧
      ∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[fun ω => f (y.1, ω) |
            reducedCoefficientObservationSigma
              {z | euclideanNorm (z - y.1) < 32 * R}] := by
  letI : StandardBorelSpace (FieldPair d) := ReductionImageV3.fieldPair_standardBorel d
  let U : Set (Vec d) := {z | euclideanNorm z < 32 * R}
  let h : FieldPair d → Vec d → ℝ := fun ω x => f (-x, translate x ω)
  have hhm : StronglyMeasurable (Function.uncurry h) :=
    (hf.comp (measurable_snd.neg.prodMk
      (Probability.continuous_translate.measurable.comp measurable_swap))).stronglyMeasurable
  let v : Vec d → FieldPair d → ℝ := fun x ω =>
    conditionalSpatialAverage (reducedCoefficientObservationSigma U)
      (reducedEnvironmentLaw Q) h ω x
  have hvm : @Measurable (Vec d × FieldPair d) ℝ
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma U)) inferInstance (Function.uncurry v) :=
    (stronglyMeasurable_conditionalSpatialAverage
      (reducedCoefficientObservationSigma U) (reducedEnvironmentLaw Q) h hhm).measurable.comp
        measurable_swap
  have hle : reducedCoefficientObservationSigma U ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : U =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hv (x : Vec d) : v x =ᵐ[reducedEnvironmentLaw Q]
      (reducedEnvironmentLaw Q)[fun ω => f (-x, translate x ω) |
        reducedCoefficientObservationSigma U] := by
    have hpres : MeasurePreserving (translate x)
        (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
      ⟨Probability.measurable_translate x, reducedEnvironmentLaw_stationary Q x⟩
    exact conditionalSpatialAverage_ae_eq_condExp (reducedCoefficientObservationSigma U)
      (reducedEnvironmentLaw Q) hle h x (hpres.integrable_comp_of_integrable (hfi (-x)))
  refine ⟨fun p => v (0 - p.1.1) (translate p.1.1 p.2), ?_, ?_⟩
  · apply measurable_centered_local_observable (U := U)
      (S := {y | euclideanNorm y ≤ R}) (W := {z | euclideanNorm z < 33 * R})
      (F := v) _ hvm (0 : Vec d)
    intro y hy z hz
    have hnorm := TimeChange.euclideanNorm_add_le y z
    change euclideanNorm y ≤ R at hy
    change euclideanNorm z < 32 * R at hz
    change euclideanNorm (y + z) < 33 * R
    linarith
  · intro y
    have hpres : MeasurePreserving (translate y.1)
        (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
      ⟨Probability.measurable_translate y.1, reducedEnvironmentLaw_stationary Q y.1⟩
    have hversion := hpres.quasiMeasurePreserving.ae_eq_comp (hv (0 - y.1))
    have hfm : Measurable (fun ω => f (-(0 - y.1), translate (0 - y.1) ω)) :=
      hf.comp (measurable_const.prodMk (Probability.measurable_translate _))
    have hfi' : Integrable (fun ω => f (-(0 - y.1), translate (0 - y.1) ω))
        (reducedEnvironmentLaw Q) := by
      have hpres' : MeasurePreserving (translate (0 - y.1))
          (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
        ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
      exact hpres'.integrable_comp_of_integrable (hfi _)
    have ht := condExp_reducedObservation_translate Q U y.1 hfm hfi'
    exact hversion.trans (by
      simpa only [Function.comp_def, translate_add, sub_add_cancel, translate_zero,
        zero_sub, neg_neg, neg_add_cancel, Set.mem_setOf_eq, U] using ht.symm)

end EinsteinRelation.Correctors
