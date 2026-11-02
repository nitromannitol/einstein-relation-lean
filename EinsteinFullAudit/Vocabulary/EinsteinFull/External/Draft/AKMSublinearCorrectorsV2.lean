import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FunProp
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMSourceFluxCorrector
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.MatrixNorm
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMCorrectorOscillation
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensitySources

/-! Vocabulary for `EinsteinFull.External.Draft.AKMSublinearCorrectorsV2`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

namespace EinsteinFull.External.Draft

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

open EinsteinRelation.External.AKM

/-- V2 removes the derived annealed cell-flux integrability premise by using
`SourceCorrector` and its literal heat-selected flux-potential carrier.
DRAFT for `external:AKM#3.17-6.2`: the oscillation and local-gradient
conclusions of Lemma 3.17, (3.85)–(3.86), printed p.100, and the flux-potential
conclusion of Proposition 6.2, (6.13), pp.249–250. The source flux object is
selected by (6.7); its existence is stated in Lemma 6.1. Only the oscillation
part of (3.85) is retained, not its negative norms or energy defect.
The random radius has the (3.39) stretched-exponential bound, with its constant
allowed to depend on s. The deterministic exponent and bound precede s and the
law. Lattice stationarity, unit range, Euclidean norms, normalized spatial
averages and source spatial correctors are literal. No horizontal or smooth
pointwise transfer, clock field or complex force occurs in this proposition. -/
def akmSublinearCorrectorsStmtV2 : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 1 < K →
    ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
    ∀ s : ℝ, 0 < s → s < d → ∃ Cs : ℝ, 0 < Cs ∧
    ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
    ∀ e : Vec d, euclideanNorm e = 1 → ∀ φ : SourceCorrector P e,
      Nonempty (Source.AKM.SourceFluxCorrector φ) ∧
      ∀ S : Source.AKM.SourceFluxCorrector φ, ∃ X : Coefficient d K → ℝ,
        Measurable X ∧ OsBound P X s Cs ∧
        ∀ᵐ a ∂P, 1 ≤ X a ∧ ∀ r : ℝ, X a ≤ r →
          Real.sqrt (⨍ x in ball 0 r,
            |φ.potential a x - (⨍ y in ball 0 r, φ.potential a y)| ^ 2) +
          Real.sqrt (⨍ x in ball 0 r,
            frobeniusNorm (S.potential a x -
              (Matrix.of fun i j => ⨍ y in ball 0 r, S.potential a y i j)) ^ 2) ≤
                C * r ^ (1 - β * ((d : ℝ) - s)) ∧
          Real.sqrt (⨍ x in ball 0 r, euclideanSq (φ.grad a x)) ≤ C

end EinsteinFull.External.Draft
