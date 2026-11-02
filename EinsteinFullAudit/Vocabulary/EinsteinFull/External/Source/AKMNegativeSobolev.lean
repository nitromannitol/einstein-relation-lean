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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMLocalCorrectors

/-! Vocabulary for `EinsteinFull.External.Source.AKMNegativeSobolev`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace EinsteinFull.External.Source.AKM

open EinsteinRelation EinsteinRelation.External.AKM

/-- The actual iterated coordinate derivative of a smooth test, with each
coordinate repeated its multi-index multiplicity. The order is fixed by the
increasing coordinate list; mixed derivatives commute on the smooth tests
used in the dual norm. -/
def multiIndexDerivative {d m : ℕ} (β : Fin d → Fin (m + 1))
    (ψ : Vec d → ℝ) : Vec d → ℝ :=
  ((List.finRange d).flatMap fun j => List.replicate (β j).val j).foldr
    coordinateDerivative ψ

/-- AKM's normalized `H^m(U)` test norm, (0.26) and (B.1).
The finite type indexes every multi-index with entries at most `m`; the
filter retains precisely total orders at most `m`. Each normalized scalar
L² norm has the source factor `|U|^((|β|-m)/d)`. -/
def integerSobolevTestNorm {d : ℕ} (m : ℕ) (U : Set (Vec d))
    (ψ : Vec d → ℝ) : ℝ :=
  ∑ β : Fin d → Fin (m + 1),
    if (∑ j : Fin d, (β j).val) ≤ m then
      (volume U).toReal ^ ((((∑ j : Fin d, (β j).val : ℕ) : ℝ) - m) / d) *
        scalarRms volume U (multiIndexDerivative β ψ)
    else 0

/-- The normalized scalar negative `H^m(U)` norm, defined by (0.29).
Absolute values give the source supremum because the test ball is symmetric.
No measurability or finiteness of a supremum is built into this definition. -/
def negativeIntegerSobolevNorm {d : ℕ} (m : ℕ) (U : Set (Vec d))
    (f : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → ℝ //
      IsSpatialTest U ψ ∧ integerSobolevTestNorm m U ψ ≤ 1},
    ENNReal.ofReal |⨍ x in U, f x * ψ.1 x ∂volume|

/-- Component sum of the scalar negative norms. This is equivalent to the
source vector norm up to a factor depending only on the dimension, absorbed
in the unspecified structural constant of (4.126). -/
def vectorNegativeIntegerSobolevNorm {d : ℕ} (m : ℕ) (U : Set (Vec d))
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ j : Fin d, negativeIntegerSobolevNorm m U (fun x => F x j)

end EinsteinFull.External.Source.AKM
