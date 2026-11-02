import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.PiL2
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
import Mathlib.Analysis.Calculus.FDeriv.Prod
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMNegativeSobolev
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensitySources
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMLocalCorrectors

/-! Vocabulary for `EinsteinFull.External.Draft.AKMNegativeSobolev`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

namespace EinsteinFull.External.Draft

open EinsteinRelation EinsteinRelation.External.AKM

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- DRAFT for graph leaf `external:AKM#4.126`: the unmollified `p = 2`
estimate following Theorem 4.24, printed pp.172–173, specialized to integer
orders `m > d/2`. Only the gradient and homogenized-centered flux occur;
the energy-density estimate requires mollification and is not asserted.
The constant depends on `d,K,m,s` and precedes the law, direction and scale.
The direction lies in the open Euclidean unit ball and `0 < ε < 1/2`.
Source spatial correctors and the variationally characterized homogenized
matrix are selected on the source law. A measurable real majorant expresses
the stochastic estimate for the extended negative norms. No Schwartz-test,
horizontal, physical, clock, or complex-force application is admitted. -/
def akmNegativeSobolevStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K : ℝ), 1 < K →
    ∀ (m : ℕ), (d : ℝ) / 2 < m → ∀ s : ℝ, 0 < s → s < 2 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
        ∃ S : SourceObjects P, ∀ e : Vec d, euclideanNorm e < 1 →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          ∃ Z : Coefficient d K → ℝ, Measurable Z ∧
            OsBound P Z s (C * ε ^ ((d : ℝ) / 2)) ∧
            ∀ᵐ a ∂P,
              Source.AKM.vectorNegativeIntegerSobolevNorm m (originBall d 1)
                (fun x => (S.corrector e).grad a (ε⁻¹ • x)) +
              Source.AKM.vectorNegativeIntegerSobolevNorm m (originBall d 1)
                (fun x => (a (ε⁻¹ • x)).mulVec
                  (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e) ≤
              ENNReal.ofReal (Z a)

end EinsteinFull.External.Draft
