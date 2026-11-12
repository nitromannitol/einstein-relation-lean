import EinsteinRelation.Correctors.ConditionalMapTransport
import EinsteinRelation.Correctors.ReducedLocalTranslationMeasurability

/-! # Translating finite-window conditional expectations

Source: `paper/main.tex:913–938`. Translation of a coefficient observation
window is identified before transporting conditional expectations under the
actual stationary reduced environment law.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Translating the environment pulls a coefficient window back to its
spatial translate. Source: `paper/main.tex:931–938`. -/
theorem reducedObservation_comap_translate {d : ℕ} (U : Set (Vec d)) (y : Vec d) :
    (reducedCoefficientObservationSigma U).comap (translate y) =
      reducedCoefficientObservationSigma {z | z - y ∈ U} := by
  apply le_antisymm
  · exact (measurable_translate_reducedObservation y (fun z hz => by
      change y + z - y ∈ U
      simpa only [add_sub_cancel_left] using hz)).comap_le
  · have hback := (measurable_translate_reducedObservation (U := {z | z - y ∈ U})
      (W := U) (-y) (fun z hz => by
        simpa only [sub_eq_add_neg, add_comm] using hz)).comap_le
    have h := MeasurableSpace.comap_mono (g := translate y) hback
    rw [MeasurableSpace.comap_comp] at h
    have hcomp : translate (-y) ∘ translate y = (id : FieldPair d → FieldPair d) := by
      funext ω
      simp only [Function.comp_apply, translate_add, neg_add_cancel, translate_zero, id_eq]
    simpa only [hcomp, MeasurableSpace.comap_id] using h

/-- Conditional expectation in a translated coefficient window commutes
with the environment translation. Source: `paper/main.tex:931–938`. -/
theorem condExp_reducedObservation_translate {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (U : Set (Vec d)) (y : Vec d)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfi : Integrable f (reducedEnvironmentLaw Q)) :
    (reducedEnvironmentLaw Q)[(fun ω => f (translate y ω)) |
        reducedCoefficientObservationSigma {z | z - y ∈ U}] =ᵐ[reducedEnvironmentLaw Q]
      (fun ω => (reducedEnvironmentLaw Q)[f |
        reducedCoefficientObservationSigma U] (translate y ω)) := by
  have hle : reducedCoefficientObservationSigma U ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    have heval : Measurable (fun (ω : FieldPair d) (x : U) => ω.1 x) :=
      measurable_pi_lambda _ fun x =>
        ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable
    exact heval.comap_le
  have hX : @Measurable (FieldPair d) (FieldPair d) (borel (FieldPair d))
      (reducedCoefficientObservationSigma U) id := measurable_id'' hle
  have hY : Measurable (translate y) := Probability.measurable_translate y
  have hfi' : Integrable f (Measure.map (translate y) (reducedEnvironmentLaw Q)) := by
    rw [reducedEnvironmentLaw_stationary Q y]
    exact hfi
  have h := @condExp_comap_comp_map (FieldPair d) (FieldPair d) (FieldPair d)
    (borel (FieldPair d)) (borel (FieldPair d)) (reducedCoefficientObservationSigma U)
    (reducedEnvironmentLaw Q) _ (translate y) hY id hX f hf hfi'
  have hcomp : (reducedCoefficientObservationSigma U).comap (id ∘ translate y) =
      reducedCoefficientObservationSigma {z | z - y ∈ U} :=
    reducedObservation_comap_translate U y
  rw [hcomp, MeasurableSpace.comap_id, reducedEnvironmentLaw_stationary Q y] at h
  exact h

/-- A version conditioned at the origin transports to a conditional
version at every center. The spatial source is the actual translation
orbit, so its covariance follows from the translation group law.
Source: `paper/main.tex:931–938`. -/
theorem translated_local_conditional_version {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (U : Set (Vec d))
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfi : Integrable f (reducedEnvironmentLaw Q))
    (v : Vec d → FieldPair d → ℝ)
    (hv : ∀ x, v x =ᵐ[reducedEnvironmentLaw Q]
      (reducedEnvironmentLaw Q)[fun ω => f (translate x ω) |
        reducedCoefficientObservationSigma U]) (x y : Vec d) :
    (fun ω => v (x - y) (translate y ω)) =ᵐ[reducedEnvironmentLaw Q]
      (reducedEnvironmentLaw Q)[fun ω => f (translate x ω) |
        reducedCoefficientObservationSigma {z | z - y ∈ U}] := by
  have hpres : MeasurePreserving (translate y)
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
    ⟨Probability.measurable_translate y, reducedEnvironmentLaw_stationary Q y⟩
  have hversion := hpres.quasiMeasurePreserving.ae_eq_comp (hv (x - y))
  have hpres' : MeasurePreserving (translate (x - y))
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
    ⟨Probability.measurable_translate (x - y),
      reducedEnvironmentLaw_stationary Q (x - y)⟩
  have htransport := condExp_reducedObservation_translate Q U y
    (hf.comp (Probability.measurable_translate (x - y)))
    (hpres'.integrable_comp_of_integrable hfi)
  exact hversion.trans (by
    simpa only [Function.comp_def, translate_add, sub_add_cancel] using htransport.symm)

end EinsteinRelation.Correctors
