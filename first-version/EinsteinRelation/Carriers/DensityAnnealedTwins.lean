import EinsteinRelation.Environment.Reduction
import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Probability.ValidAnnealedLawSupport
import EinsteinRelation.Regeneration.Coupling
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Exponential

/-! # Production twins of the density and annealed-law carriers

Each definition here mirrors a frozen definition under `EinsteinRelation/Frozen/`.
Production modules may not import the frozen files, so every body is copied from
its frozen counterpart. The only replacements are these: references to other
frozen definitions point to the twins in this file, and the frozen structure
arguments `CoordinatePathLawInput` and `CoupledPathLawInput` are replaced by the
fields their bodies use. The dimension hypothesis `hd` is dropped because no
body uses it. The two structures themselves are not twinned.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace EinsteinRelation.Carriers

/-- The reduced coefficient and clock law induced by the physical environment law.
Production twin of `EinsteinRelation.Frozen.DensityCarriers.reducedReferenceLaw`
(`EinsteinRelation/Frozen/DensityCarriers/ReducedReferenceLaw.lean`), with the same body. -/
def reducedReferenceLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : Measure (FieldPair d) :=
  Measure.map reduce Q.measure

/-- The reduced environment observed at time `t` along a continuous path.
Production twin of `EinsteinRelation.Frozen.DensityCarriers.reducedObservationAt`
(`EinsteinRelation/Frozen/DensityCarriers/ReducedObservationAt.lean`), with the same body. -/
def reducedObservationAt {d : ℕ} (t : ℝ≥0)
    (z : FieldPair d × Path d) : FieldPair d :=
  reduce (translate (pathPosition t z.2) z.1)

open EinsteinRelation.Probability.ValidAnnealedLawSupport

/-- The annealed joint environment and physical path law at the origin.
Production twin of `EinsteinRelation.Frozen.ValidAnnealedLawCarriers.annealedCoordinateJoint`
(`EinsteinRelation/Frozen/ValidAnnealedLawCarriers/AnnealedCoordinateJoint.lean`), with the
coordinate-path input replaced by its fields `Q`, `P`, `origin_probability`. -/
def annealedCoordinateJoint {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) :
    Measure (FieldPair d × Path d) :=
  annealedJointOnProbabilityFibers Q (originLaw P) origin_probability

/-- The physical path marginal of the annealed coordinate/environment law.
Production twin of
`EinsteinRelation.Frozen.ValidAnnealedLawCarriers.annealedCoordinatePathProjection`
(`EinsteinRelation/Frozen/ValidAnnealedLawCarriers/AnnealedCoordinatePathProjection.lean`),
with the coordinate-path input replaced by its fields `Q`, `P`, `origin_probability`. -/
def annealedCoordinatePathProjection {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) :
    Measure (Path d) :=
  (annealedCoordinateJoint Q P origin_probability).map Prod.snd

/-- The annealed joint environment and coupled path/Bernoulli law at the origin.
Production twin of `EinsteinRelation.Frozen.ValidAnnealedLawCarriers.annealedCoupledJoint`
(`EinsteinRelation/Frozen/ValidAnnealedLawCarriers/AnnealedCoupledJoint.lean`), with the
coupled-path input replaced by its fields `Q`, `K`, `origin_probability`. -/
def annealedCoupledJoint {d : ℕ} (Q : Measure (FieldPair d))
    (K : Regeneration.CoupledQuenchedLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (Regeneration.originCoupledLaw K ω)) :
    Measure (FieldPair d × Regeneration.CoupledSample d) :=
  annealedJointOnProbabilityFibers Q (Regeneration.originCoupledLaw K) origin_probability

/-- The path marginal of the annealed coupled environment/sample law.
Production twin of `EinsteinRelation.Frozen.ValidAnnealedLawCarriers.annealedCoupledPathProjection`
(`EinsteinRelation/Frozen/ValidAnnealedLawCarriers/AnnealedCoupledPathProjection.lean`),
with the coupled-path input replaced by its fields `Q`, `K`, `origin_probability`. -/
def annealedCoupledPathProjection {d : ℕ} (Q : Measure (FieldPair d))
    (K : Regeneration.CoupledQuenchedLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (Regeneration.originCoupledLaw K ω)) :
    Measure (Path d) :=
  (annealedCoupledJoint Q K origin_probability).map (Prod.fst ∘ Prod.snd)

/-- The law of the reduced environment observed at a fixed nonnegative time.
Production twin of `EinsteinRelation.Frozen.DensityCarriers.reducedObservedLaw`
(`EinsteinRelation/Frozen/DensityCarriers/ReducedObservedLaw.lean`), with the
coordinate-path input replaced by its fields `Q`, `P`, `origin_probability`. -/
def reducedObservedLaw {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (t : ℝ≥0) : Measure (FieldPair d) :=
  (annealedCoordinateJoint Q P origin_probability).map (reducedObservationAt t)

/-- The reduced environment law at an independent exponential time of positive rate.
Production twin of `EinsteinRelation.Frozen.DensityCarriers.reducedLaplaceObservedLaw`
(`EinsteinRelation/Frozen/DensityCarriers/ReducedLaplaceObservedLaw.lean`), with the
coordinate-path input replaced by its fields `Q`, `P`, `origin_probability`. -/
def reducedLaplaceObservedLaw {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) : Measure (FieldPair d) :=
  ((ProbabilityTheory.expMeasure s.1).prod
      (annealedCoordinateJoint Q P origin_probability)).map
    (fun z : ℝ × (FieldPair d × Path d) =>
      reducedObservationAt z.1.toNNReal z.2)

/-- A nonnegative measurable density `rho` of the reduced Laplace-time law
`reducedLaplaceObservedLaw Q P origin_probability s` with respect to the reduced reference law
of the environment law `Q`, which is `Measure.map reduce Q`, the body of `reducedReferenceLaw`
(source: `paper/main.tex:198-208` for `reduce`, `237-240` for the reduced canonical space,
`431-437` for `ρ_s` as the density of the law of the environment at an exponential time).
Production twin of `EinsteinRelation.Frozen.DensityCarriers.IsReducedLaplaceDensity`
(`EinsteinRelation/Frozen/DensityCarriers/IsReducedLaplaceDensity.lean`), with the
coordinate-path input replaced by its fields `Q`, `P`, `origin_probability`. -/
def IsReducedLaplaceDensity {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ) : Prop :=
  Measurable rho ∧ (∀ w, 0 ≤ rho w) ∧
    reducedLaplaceObservedLaw Q P origin_probability s =
      (Measure.map EinsteinRelation.reduce Q).withDensity (fun w => ENNReal.ofReal (rho w))

end EinsteinRelation.Carriers
