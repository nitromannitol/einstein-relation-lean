import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Draft.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMCoarsenedObjects
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMSelectedLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMLocalCorrectors

/-! Vocabulary for `EinsteinFull.External.Draft.AKMBlockEstimates`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

namespace EinsteinFull.External.Draft

open EinsteinRelation EinsteinRelation.External.AKM

open EinsteinRelation.Environment.AKMTestIntegralSupport

open EinsteinFull.External.Source.AKM

/-- DRAFT graph leaf external:AKM#5.29i. Source Lemma5.29(i), (5.90),
printed p.222. This is the genuine centered quadratic energy, without matrix
polarization, physical rescaling, a clock coordinate or an L2 transfer.
The source r>=1 range is restricted to the explicit construction's r>=2. -/
def akmBlockCltStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (K s δ γ η : ℝ) (hK : 1 < K), ∀ h : blockParameterWindow d s δ γ η,
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (Coefficient d K)) (hP : LawHypotheses P),
      let J := sourceSelectedLocalizedEnergy d hd K s δ γ hK
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 P hP
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ η ≤ r → r ≤ R →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
      OsBound P (fun a => |sourceCenteredBlock P J a z R r f p q|)
        s (C * R ^ (-(d : ℝ) / 2))

/-- DRAFT graph leaf external:AKM#5.29ii. Source Lemma5.29(ii),
(5.91)--(5.92), printed p.223. The allowed smoothing interval is
[R^(beta*eta), R^(beta/(1+delta))]; the integral uses the outer cube's volume.
No estimate is asserted for a clock coordinate or a joint matrix block. -/
def akmBlockBoundaryStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (K s δ γ η : ℝ) (hK : 1 < K), ∀ h : blockParameterWindow d s δ γ η,
    ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (Coefficient d K)) (hP : LawHypotheses P),
      let J := sourceSelectedLocalizedEnergy d hd K s δ γ hK
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 P hP
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ r → R ^ (β * η) ≤ r →
        r ≤ R ^ (β / (1 + δ)) →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
        Function.support f ⊆ sourceBlockCube z R \ sourceBlockCube z (R - R ^ β) →
      OsBound P (fun a => |sourceCenteredBlock P J a z R r f p q|)
        s (C * R ^ (-(d : ℝ) / 2 - (1 - β) / 2))

/-- DRAFT graph leaf external:AKM#5.29iii. Source Lemma5.29(iii), printed
p.223. The positive gain is chosen before ellipticity K, as in the source.
Both terms use the SAME centered source family; this is an Os bound on the
volume average, not a Gaussian or joint covariance conclusion. -/
def akmBlockChangeStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (s δ γ η : ℝ),
    ∀ h : blockParameterWindow d s δ γ η,
    ∀ β : ℝ, η ≤ β → β < 1 →
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (K : ℝ) (hK : 1 < K), ∃ C : ℝ, 0 < C ∧
    ∀ (P : Measure (Coefficient d K)) (hP : LawHypotheses P),
      let J := sourceSelectedLocalizedEnergy d hd K s δ γ hK
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 P hP
      ∀ (R r : ℝ), 1 ≤ R → 2 ≤ R ^ η → R ^ η ≤ r → r ≤ R ^ β →
      ∀ (z p q : Vec d), euclideanNorm p < 1 → euclideanNorm q < 1 →
      OsBound P (fun a => |sourceCenteredBlock P J a z R r (fun _ => 1) p q -
          sourceCenteredBlock P J a z R (R ^ η) (fun _ => 1) p q|)
        s (C * R ^ (-(d : ℝ) / 2 - ε))

end EinsteinFull.External.Draft
