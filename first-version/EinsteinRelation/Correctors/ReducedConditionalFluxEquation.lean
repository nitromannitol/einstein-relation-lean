import EinsteinRelation.Correctors.ConditionalFluxEquation
import EinsteinRelation.Correctors.LocalFluxMeasurability
import EinsteinRelation.Correctors.CoefficientLawEllipticity
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import EinsteinRelation.Mobility.DriftBoundPointwise
import EinsteinRelation.Environment.ReductionImageSupport

/-! # Conditioning the actual reduced coefficient equation

Source: `paper/main.tex:913–925`. The reduced law supplies the coefficient
bounds, and coefficient observation supplies the pullout property on the
observed spatial region. Neither is an additional premise on the correctors.
-/

open MeasureTheory ProbabilityTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- The actual reduced coefficient is bounded at every spatial point on one
full-measure event. Source: `paper/main.tex:198–207,919–925`. -/
theorem ae_reduced_coefficient_entry_bound {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ x : Vec d, ∀ j k : Fin d,
      |ω.1 x j k| ≤ Real.exp (2 * L) * L := by
  have hmap : Measure.map (Prod.fst : FieldPair d → CoefficientField d)
      (reducedEnvironmentLaw Q) = coefficientLaw Q.measure := by
    unfold reducedEnvironmentLaw coefficientLaw
    rw [Measure.map_map continuous_fst.measurable Probability.measurable_reduce]
    rfl
  have he := ae_coefficientLaw_isElliptic Q
  rw [← hmap] at he
  have he' := ae_of_ae_map continuous_fst.measurable.aemeasurable he
  have hK : 0 ≤ Real.exp (2 * L) * L :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  filter_upwards [he'] with ω hω
  intro x j k
  apply abs_entry_le_of_quadratic_bounds hK (ω.1 x) (hω x).1
  · intro ξ
    exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans
      ((hω x).2 ξ).1
  · exact fun ξ => ((hω x).2 ξ).2

/-- Multiplication by the actual reduced coefficient preserves product
integrability. Source: `paper/main.tex:919–925`. -/
theorem integrable_reduced_coefficient_mul {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (U : Set (Vec d))
    {f : FieldPair d × Vec d → ℝ}
    (hf : Integrable f ((reducedEnvironmentLaw Q).prod (volume.restrict U)))
    (j k : Fin d) :
    Integrable (fun z : FieldPair d × Vec d => z.1.1 z.2 j k * f z)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)) := by
  have hm : Measurable (fun z : FieldPair d × Vec d => z.1.1 z.2 j k) :=
    ((continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).matrix_elem j k).measurable
  apply hf.bdd_mul (c := Real.exp (2 * L) * L) hm.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).mpr
  filter_upwards [ae_reduced_coefficient_entry_bound Q] with ω hω
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hω x j k

/-- Conditioning on the coefficient observations of the domain preserves
the original gradient and flux equations. All coefficient measurability,
observation and product bounds are derived for the actual environment law.
Source: `paper/main.tex:913–925`. -/
theorem hasWeakGradient_and_flux_reduced_conditional {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (U : Set (Vec d)) (hU : MeasurableSet U)
    [IsFiniteMeasure (volume.restrict U)]
    (u : FieldPair d → Vec d → ℝ) (G : FieldPair d → Vec d → Vec d)
    (S : FieldPair d → Vec d → Mat d) (e b : Vec d)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hGm : ∀ k, StronglyMeasurable (fun z : FieldPair d × Vec d => G z.1 z.2 k))
    (hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
    (hui : Integrable (Function.uncurry u)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)))
    (hGi : ∀ k, Integrable (fun z : FieldPair d × Vec d => G z.1 z.2 k)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)))
    (hSi : ∀ j k, Integrable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)))
    (hgrad : ∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakGradient U (u ω) (G ω))
    (hflux : ∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakRowDivergence U (S ω)
      (fun x => (ω.1 x).mulVec (e + G ω x) - b)) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient U
        (conditionalSpatialAverage (reducedCoefficientObservationSigma U)
          (reducedEnvironmentLaw Q) u ω)
        (fun x k => conditionalSpatialAverage (reducedCoefficientObservationSigma U)
          (reducedEnvironmentLaw Q) (fun a y => G a y k) ω x) ∧
      HasWeakRowDivergence U
        (fun x j k => conditionalSpatialAverage (reducedCoefficientObservationSigma U)
          (reducedEnvironmentLaw Q) (fun a y => S a y j k) ω x)
        (fun x => (ω.1 x).mulVec
          (e + fun k => conditionalSpatialAverage (reducedCoefficientObservationSigma U)
            (reducedEnvironmentLaw Q) (fun a y => G a y k) ω x) - b) := by
  have hm : reducedCoefficientObservationSigma U ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : U =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  apply hasWeakGradient_and_flux_conditional (reducedCoefficientObservationSigma U)
    (reducedEnvironmentLaw Q) hm U (fun a x => a.1 x) u G S e b
    (fun j k => ((continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).matrix_elem j k).measurable)
    hum hGm hSm _ _ hui hGi hSi hgrad hflux
  · intro j k
    filter_upwards [ae_restrict_mem hU] with x hx
    exact (((continuous_id : Continuous (fun A : Mat d => A)).matrix_elem j k).measurable.comp
      (measurable_reduced_coefficient_evaluation hx)).stronglyMeasurable
  · intro j k
    exact integrable_reduced_coefficient_mul Q U ((integrable_const (e k)).add (hGi k)) j k

end EinsteinRelation.Correctors
