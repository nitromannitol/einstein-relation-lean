import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Correctors.StationaryParameterIntegrability
import EinsteinRelation.Correctors.ReducedConditionalFluxEquation

/-! # Integrability of canonical gradient orbit coordinates

Source: `paper/main.tex:913–925`. A fixed coordinate of an `L²` field, evaluated
along stationary orbit translations and integrated against a finite measure on
the translation parameter, is integrable.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
noncomputable section
namespace EinsteinRelation.Correctors

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- Coordinate of an `L²` field along stationary orbit translations is integrable
against any finite measure on the translation parameter. -/
theorem integrable_lp_orbit_coordinate {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (k : Fin d)
    (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)] :
    Integrable (fun z : FieldPair d × Vec d => (G (translate z.2 z.1)).ofLp k)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)) := by
  have hQ : IsStationary (reducedEnvironmentLaw Q) := reducedEnvironmentLaw_stationary Q
  have hGm : Measurable fun ω : FieldPair d => G ω := (Lp.stronglyMeasurable G).measurable
  have hc : Measurable fun v : EuclideanSpace ℝ (Fin d) => v.ofLp k :=
    (measurable_pi_apply k).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous.measurable
  have hf : Measurable fun ω : FieldPair d => (G ω).ofLp k := hc.comp hGm
  have hfi : Integrable (fun ω : FieldPair d => (G ω).ofLp k) (reducedEnvironmentLaw Q) := by
    refine Integrable.mono' ((Lp.memLp G).integrable (by norm_num)).norm
      hf.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    exact PiLp.norm_apply_le (G ω) k
  have h := integrable_stationary_param (T := id) hQ (volume.restrict U) measurable_id
    (a := fun _ : Vec d => (1 : ℝ)) measurable_const (integrable_const (1 : ℝ)) hf hfi
  simpa only [one_mul, id_eq] using h

/-- The `k`-th coordinate of the canonical corrector gradient is integrable along
stationary orbit translations against any finite measure on the translation parameter
(`paper/main.tex:913–925`). -/
theorem integrable_canonicalGradient_orbit_coordinate {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i k : Fin d) (U : Set (Vec d))
    [IsFiniteMeasure (volume.restrict U)] :
    Integrable (fun z : FieldPair d × Vec d =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate z.2 z.1)).ofLp k)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)) :=
  integrable_lp_orbit_coordinate Q (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) k U

/-- The local conditional versions of an actual canonical scalar/skew pair
satisfy the canonical gradient and constitutive flux equations. The canonical
gradient's measurability and product integrability follow from its actual L²
class and stationarity. Source: `paper/main.tex:913–925`. -/
theorem hasWeakGradient_and_flux_canonical_conditional {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (U : Set (Vec d)) (hU : MeasurableSet U) [IsFiniteMeasure (volume.restrict U)]
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
    (hui : Integrable (Function.uncurry u)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)))
    (hSi : ∀ j k, Integrable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)
      ((reducedEnvironmentLaw Q).prod (volume.restrict U)))
    (hgrad : ∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakGradient U (u ω)
      (fun x => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate x ω)).ofLp))
    (hflux : ∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakRowDivergence U (S ω)
      (fun x => (ω.1 x).mulVec (unitVector i +
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) - (expectedCorrectorFlux Q i).ofLp)) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient U
        (conditionalSpatialAverage (reducedCoefficientObservationSigma U)
          (reducedEnvironmentLaw Q) u ω)
        (fun x k => conditionalSpatialAverage (reducedCoefficientObservationSigma U)
          (reducedEnvironmentLaw Q) (fun a y =>
            ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
              (reducedEnvironmentLaw Q)) (translate y a)).ofLp k) ω x) ∧
      HasWeakRowDivergence U
        (fun x j k => conditionalSpatialAverage (reducedCoefficientObservationSigma U)
          (reducedEnvironmentLaw Q) (fun a y => S a y j k) ω x)
        (fun x => (ω.1 x).mulVec (unitVector i +
          fun k => conditionalSpatialAverage (reducedCoefficientObservationSigma U)
            (reducedEnvironmentLaw Q) (fun a y =>
              ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
                (reducedEnvironmentLaw Q)) (translate y a)).ofLp k) ω x) -
          (expectedCorrectorFlux Q i).ofLp) := by
  let G : FieldPair d → Vec d → Vec d := fun a x =>
    ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
      (reducedEnvironmentLaw Q)) (translate x a)).ofLp
  have hGm : Measurable (Function.uncurry G) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      ((Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp
          (Probability.continuous_translate.measurable.comp measurable_swap))
  exact hasWeakGradient_and_flux_reduced_conditional Q U hU u G S (unitVector i)
    (expectedCorrectorFlux Q i).ofLp hum
    (fun k => ((continuous_apply k).measurable.comp hGm).stronglyMeasurable) hSm
    hui (fun k => integrable_canonicalGradient_orbit_coordinate Q i k U) hSi hgrad hflux

end EinsteinRelation.Correctors
