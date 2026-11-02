import EinsteinRelation.Environment.Basic
import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Correctors.ActualImageVariationalSupport
import EinsteinRelation.Correctors.CenteredCorrectorFluxSupport
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import Mathlib.Probability.ConditionalProbability

/-! # Production twins of frozen regeneration and corrector carriers

Each definition below repeats the body of a frozen definition under
`EinsteinRelation/Frozen/`, so that production modules can use the carrier without
importing the frozen tree. Frozen carriers whose body already exists in production
are not repeated here; they are used directly:

* `PathLawCarriers.BernoulliTrials` is `Regeneration.BernoulliSequence`;
* `PathLawCarriers.ContinuousPath` is `Path`;
* `PathLawCarriers.CoordinatePathLaw` is `QuenchedPathLaws`;
* `PathLawCarriers.coordinateLawAtOrigin` is `originLaw`;
* `PathLawCarriers.CoupledCoordinateLaw` is `Regeneration.CoupledQuenchedLaws`;
* `PathLawCarriers.CoupledPathSample` is `Regeneration.CoupledSample`;
* `PathLawCarriers.coupledLawAtOrigin` is `Regeneration.originCoupledLaw`.

The corrector predicates `NormalizedScalarCorrector` and `HeatSelectedSkewCorrectorColumn`
also have production definitions, so they have no twin here.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Carriers

/-- The source environment setting for Theorem 1.2 on the joint physical
coefficient/potential law. The spatial regularity conditions hold almost surely;
stationarity and finite range are conditions on the joint law.
Mirrors `EinsteinRelation/Frozen/EnvironmentAdmissible.lean`. -/
def EnvironmentAdmissible {d : ℕ} (Λ₀ r₀ : ℝ)
    (Q : Measure (FieldPair d)) : Prop :=
  2 ≤ d ∧
  1 ≤ Λ₀ ∧
  1 ≤ r₀ ∧
  IsProbabilityMeasure Q ∧
  (∀ᵐ ω ∂Q,
    (∀ x : Vec d,
      (ω.1 x).transpose = ω.1 x ∧
      ∀ ξ : Vec d,
        Λ₀⁻¹ * euclideanSq ξ ≤ dot ξ ((ω.1 x).mulVec ξ) ∧
        dot ξ ((ω.1 x).mulVec ξ) ≤ Λ₀ * euclideanSq ξ) ∧
    (∀ x : Vec d, |ω.2 x| ≤ Λ₀) ∧
    (∀ x y ξ : Vec d,
      euclideanNorm ((ω.1 x - ω.1 y).mulVec ξ) ≤
        Λ₀ * euclideanNorm (x - y) * euclideanNorm ξ) ∧
    (∀ x y : Vec d,
      |ω.2 x - ω.2 y| ≤ Λ₀ * euclideanNorm (x - y))) ∧
  (∀ x : Vec d, Measure.map (translate x) Q = Q) ∧
  (∀ U W : Set (Vec d),
    MeasurableSet U → MeasurableSet W →
    (∃ s : ℝ, r₀ < s ∧ ∀ x ∈ U, ∀ y ∈ W, s ≤ euclideanNorm (x - y)) →
    ProbabilityTheory.Indep (localSigma U) (localSigma W) Q)

section CycleConditioning

open EinsteinRelation.Regeneration

/-- The source no-backtracking event on the actual annealed environment/sample space.
Mirrors `EinsteinRelation/Frozen/Regeneration/CycleConditioningEvent.lean`. -/
def cycleConditioningEvent {d : ℕ} (hd : 2 ≤ d) (R : ℝ) :
    Set (FieldPair d × CoupledSample d) :=
  {ωz | NoBacktracking R ωz.2.1 ⟨0, by omega⟩}

/-- The literal law conditioned on the actual no-backtracking event, with its positive
mass explicit. Mirrors `EinsteinRelation/Frozen/Regeneration/CycleConditionedLaw.lean`. -/
noncomputable def cycleConditionedLaw {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (hd : 2 ≤ d) (R : ℝ)
    (hD : (annealedCoupledLaw Q K) (cycleConditioningEvent hd R) ≠ 0) :
    {μ : Measure (FieldPair d × CoupledSample d) // IsProbabilityMeasure μ} := by
  letI : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  exact ⟨ProbabilityTheory.cond (annealedCoupledLaw Q K) (cycleConditioningEvent hd R),
    ProbabilityTheory.cond_isProbabilityMeasure hD⟩

end CycleConditioning

/-- The stationary potential gradient of the scalar corrector on the actual reduced image law.
Mirrors `EinsteinRelation/Frozen/Correctors/CanonicalScalarCorrectorGradient.lean`. -/
noncomputable def canonicalScalarCorrectorGradient
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ActualImageVariationalSupport.imagePotentialGradientDomain Q :=
  ActualImageVariationalSupport.imageCanonicalCorrectorGradient Q i

/-- The centered corrector flux as an element of `L²` of the reduced environment law.
Mirrors `EinsteinRelation/Frozen/Correctors/CenteredCorrectorFlux.lean`. -/
noncomputable def centeredCorrectorFlux
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 2
      (EinsteinRelation.Correctors.reducedEnvironmentLaw Q) :=
  EinsteinRelation.Correctors.canonicalCenteredCorrectorFlux Q i

/-- The homogenized coefficient column, the expected corrector flux.
Mirrors `EinsteinRelation/Frozen/Correctors/HomogenizedCoefficientColumn.lean`. -/
noncomputable def homogenizedCoefficientColumn
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  EinsteinRelation.Correctors.expectedCorrectorFlux Q i

/-- The coefficient-only observation sigma algebra on a reduced environment.
Mirrors `EinsteinRelation/Frozen/Correctors/ReducedCoefficientObservationSigma.lean`. -/
def reducedCoefficientObservationSigma {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace (FieldPair d) :=
  ⨆ x : U, MeasurableSpace.comap (fun ω : FieldPair d => ω.1 x) inferInstance

end EinsteinRelation.Carriers
