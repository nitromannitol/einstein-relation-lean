import EinsteinRelation.Correctors.OriginFluxRepresentative
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:808–816`. The actual spatial coefficient
flux agrees with the affine L² flux on one event of probability one,
almost everywhere in space. -/
theorem ae_spatial_correctorFluxOfGradient {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (correctorFluxOfGradient Q i G (translate x ω)).ofLp =
        (ω.1 x).mulVec (correctorUnitVector i + G (translate x ω)).ofLp := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have h0 := ae_origin_correctorFluxOfGradient Q i G
  have hm : MeasurableSet {p : Vec d × FieldPair d |
      (correctorFluxOfGradient Q i G (translate p.1 p.2)).ofLp =
        (p.2.1 p.1).mulVec (correctorUnitVector i + G (translate p.1 p.2)).ofLp} := by
    have ht : Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) :=
      Probability.continuous_translate.measurable
    have hf := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      ((Lp.stronglyMeasurable (correctorFluxOfGradient Q i G)).measurable.comp ht)
    have hg : Measurable (fun p : Vec d × FieldPair d =>
        (correctorUnitVector i + G (translate p.1 p.2)).ofLp) :=
      (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
        (measurable_const.add ((Lp.stronglyMeasurable G).measurable.comp ht))
    have ha : Measurable (fun p : Vec d × FieldPair d => p.2.1 p.1) := by
      have h := ((continuous_eval_const (0 : Vec d)).comp continuous_fst).measurable.comp ht
      simpa only [Function.comp_def, translate_matrix, add_zero] using h
    apply measurableSet_eq_fun hf
    unfold Matrix.mulVec dotProduct
    fun_prop
  apply (Measure.ae_ae_comm hm).1
  exact ae_of_all _ fun x => by
    have h := (measurePreserving_translate (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) x).quasiMeasurePreserving.ae h0
    simpa only [translate_matrix, add_zero] using h

end EinsteinRelation.Correctors
