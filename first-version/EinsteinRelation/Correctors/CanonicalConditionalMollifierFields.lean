import EinsteinRelation.Correctors.CenteredMollifierLocality
import EinsteinRelation.Correctors.CenteredMollifierSpatialAssembly
import EinsteinRelation.Correctors.CanonicalGradientConditionalEquation
import EinsteinRelation.Correctors.ConditionalSpatialIntegrability
import EinsteinRelation.Correctors.SpatialBallVolume

/-! # One conditional source pair for the local spatial construction

Source: `paper/main.tex:913–938`. The source scalar and skew field are
conditioned jointly in space at center zero. The same conditional versions
define all five fields, their coefficient locality and their spatial weak
equations. All source existence and moment estimates remain explicit
internal obligations.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- The literal five averages of the conditional canonical source fields.
Source: `paper/main.tex:913–938`. -/
noncomputable def canonicalConditionalMollifierFields {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (R : ℝ)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d) :
    LocalCorrectorFields d :=
  centeredMollifierFields R
    (conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) u)
    (fun ω x j => conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) (fun a z =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate z a)).ofLp j) ω x)
    (fun ω x j k => conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q)
      (fun a z => S a z j k) ω x)

/-- Joint measurability of the source pair suffices for locality of all
five selected fields; no moment or equation assumption is used.
Source: `paper/main.tex:921–938`. -/
theorem measurable_canonicalConditionalMollifierFields {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (hR : 0 < R)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)) :
    let f := canonicalConditionalMollifierFields Q i R u S
    let obs := reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 33 * R}
    Measurable[obs] f.scalar ∧ Measurable[obs] f.skew ∧
      Measurable[obs] f.gradientAverage ∧ Measurable[obs] f.scalarCorrection ∧
      Measurable[obs] f.skewCorrection := by
  have hGm (j : Fin d) : StronglyMeasurable (fun z : FieldPair d × Vec d =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate z.2 z.1)).ofLp j) :=
    (((continuous_apply j).comp (PiLp.continuous_ofLp (p := 2)
      (β := fun _ : Fin d => ℝ))).measurable.comp
      ((Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp
          (Probability.continuous_translate.measurable.comp measurable_swap))).stronglyMeasurable
  exact measurable_centeredMollifierFields hR _ _ _
    ((stronglyMeasurable_conditionalSpatialAverage _ _ u hum).measurable.comp measurable_swap)
    (fun j => (stronglyMeasurable_conditionalSpatialAverage _ _
      (fun a z => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate z a)).ofLp j) (hGm j)).measurable.comp measurable_swap)
    (fun j k => (stronglyMeasurable_conditionalSpatialAverage _ _
      (fun a z => S a z j k) (hSm j k)).measurable.comp measurable_swap)

/-- Pointwise skewness of the source pair gives pointwise skewness of the
same selected skew average, including exceptional environments.
Source: `paper/main.tex:921–938`. -/
theorem canonicalConditionalMollifierFields_skew {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (R : ℝ)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    (hS : ∀ ω x, (S ω x).transpose = -(S ω x)) (ω : FieldPair d) :
    ((canonicalConditionalMollifierFields Q i R u S).skew ω).transpose =
      -(canonicalConditionalMollifierFields Q i R u S).skew ω :=
  centeredMollifierFields_skew R _ _ _
    (fun a x => conditionalSpatialAverage_skew _ _ S hS a x) ω

/-- Conditioning the actual canonical weak equations and averaging over
centers yields the spatial equations for the same five fields. Source
product integrability supplies every integrability premise of the assembly.
Source: `paper/main.tex:913–938`. -/
theorem ae_canonicalConditionalMollifierFields_spatial_equations
    {d : ℕ} {L r₀ R : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) (hR : 0 < R)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
    (hui : Integrable (Function.uncurry u) ((reducedEnvironmentLaw Q).prod
      (volume.restrict {x : Vec d | euclideanNorm x < 32 * R})))
    (hSi : ∀ j k, Integrable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)
      ((reducedEnvironmentLaw Q).prod
        (volume.restrict {x : Vec d | euclideanNorm x < 32 * R})))
    (hgrad : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient {x : Vec d | euclideanNorm x < 32 * R} (u ω)
        (fun x => ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x ω)).ofLp))
    (hflux : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakRowDivergence {x : Vec d | euclideanNorm x < 32 * R} (S ω)
        (fun x => (ω.1 x).mulVec (unitVector i +
          ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) -
          (expectedCorrectorFlux Q i).ofLp)) :
    let f := canonicalConditionalMollifierFields Q i R u S
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (orbit f.scalar ω)
        (fun x => f.gradient (translate x ω)) ∧
      HasWeakRowDivergence Set.univ (fun x => f.skew (translate x ω))
        (fun x => (ω.1 x).mulVec (unitVector i + f.gradient (translate x ω)) -
          (expectedCorrectorFlux Q i).ofLp - f.flux (translate x ω)) := by
  let B : Set (Vec d) := {x | euclideanNorm x < 32 * R}
  let m := reducedCoefficientObservationSigma B
  letI : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hB : MeasurableSet B :=
    (isOpen_lt Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  have hV : 0 < (volume B).toReal := by
    simpa only [Measure.real, External.AKM.ball, sub_zero] using
      ball_volume_pos_finite d (32 * R) (by positivity)
  letI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hV).2.ne
  have hm : m ≤ borel (FieldPair d) := by
    change reducedCoefficientObservationSigma B ≤ _
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : B =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hGm (j : Fin d) : StronglyMeasurable (fun z : FieldPair d × Vec d =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate z.2 z.1)).ofLp j) :=
    (((continuous_apply j).comp (PiLp.continuous_ofLp (p := 2)
      (β := fun _ : Fin d => ℝ))).measurable.comp
      ((Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp
          (Probability.continuous_translate.measurable.comp measurable_swap))).stronglyMeasurable
  exact ae_centeredMollifierFields_spatial_equations Q hR _ _ _
    (unitVector i) (expectedCorrectorFlux Q i).ofLp
    (integrable_conditionalSpatialAverage_product m _ hm _ u hum hui)
    (fun j => integrable_conditionalSpatialAverage_product m _ hm _
      (fun a z => ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate z a)).ofLp j) (hGm j)
      (integrable_canonicalGradient_orbit_coordinate Q i j B))
    (fun j k => integrable_conditionalSpatialAverage_product m _ hm _
      (fun a z => S a z j k) (hSm j k) (hSi j k))
    (hasWeakGradient_and_flux_canonical_conditional Q i B hB u S hum hSm hui hSi hgrad hflux)

end EinsteinRelation.Correctors
