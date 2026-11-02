import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.List
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Basic.Denumerable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Convex.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Smooth
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Probability.ProbabilityPart

/-! Vocabulary for `EinsteinFull.External.Draft.BassFoundation`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory ProbabilityTheory

open scoped BigOperators Topology NNReal

namespace EinsteinFull.External.Bass

open EinsteinRelation

/-- Source continuous paths, before equipping them with the cylindrical sigma algebra.
A separate carrier prevents the frozen path carrier's Borel instance from silently
choosing the source sigma algebra. -/
structure Path (d : ℕ) where
  /-- The continuous map represented by a source canonical path. -/
  toContinuousMap : C(ℝ≥0, Vec d)

instance {d : ℕ} : CoeFun (Path d) (fun _ => ℝ≥0 → Vec d) :=
  ⟨fun γ => γ.toContinuousMap⟩

/-- The source sigma algebra is generated by all coordinate evaluations. -/
instance (d : ℕ) : MeasurableSpace (Path d) :=
  ⨆ t : ℝ≥0, (inferInstance : MeasurableSpace (Vec d)).comap (fun γ : Path d => γ t)

/-- Every coordinate evaluation is measurable for the cylindrical sigma algebra. -/
theorem measurable_eval {d : ℕ} (t : ℝ≥0) :
    Measurable (fun γ : Path d => γ t) := by
  apply measurable_iff_comap_le.mpr
  exact le_iSup (fun s : ℝ≥0 => (inferInstance : MeasurableSpace (Vec d)).comap
    (fun γ : Path d => γ s)) t

/-- The raw coordinate filtration on source cylindrical paths. -/
noncomputable def rawFiltration (d : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Path d)) :=
  Filtration.natural (fun t (γ : Path d) => γ t)
    (fun t => (measurable_eval t).stronglyMeasurable)

/-- Bass's right-continuous canonical filtration, without probability completion. -/
noncomputable def filtration (d : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Path d)) :=
  (rawFiltration d).rightCont

/-- The source filtration is right continuous by construction. -/
instance (d : ℕ) : (filtration d).IsRightContinuous := by
  unfold filtration
  infer_instance

/-- The nondivergence-form operator in Bass V.1: the factor one half multiplies
only the diffusion term; drift is neither symmetrized nor differentiated. -/
noncomputable def generator {d : ℕ} (a : Vec d → Mat d) (b : Vec d → Vec d)
    (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j *
      fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) +
    ∑ i, b x i * fderiv ℝ f x (unitVector i)

/-- The source compensated process on actual continuous coordinate paths. -/
noncomputable def compensatedTest {d : ℕ} (a : Vec d → Mat d) (b : Vec d → Vec d)
    (f : Vec d → ℝ) (t : ℝ≥0) (γ : Path d) : ℝ :=
  f (γ t) - f (γ 0) - ∫ u in (0 : ℝ)..(t : ℝ), generator a b f (γ u.toNNReal)

open Filter Set

open scoped Convolution Pointwise

end EinsteinFull.External.Bass

namespace EinsteinFull

open EinsteinRelation

end EinsteinFull
