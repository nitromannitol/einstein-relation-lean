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
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Draft.BassFoundation
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Smooth
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Probability.ProbabilityPart

/-! Vocabulary for `EinsteinFull.Calculus.C8BassFiltrationCompletion`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory ProbabilityTheory

open scoped NNReal Topology

namespace EinsteinFull.External.Bass.Completion

open EinsteinRelation

/-- The ambient null sets, including subsets of measurable null sets. -/
@[instance_reducible]
def nullSets {d : ℕ} (P : Measure (Bass.Path d)) : MeasurableSpace (Bass.Path d) :=
  MeasurableSpace.generateFrom {A : Set (Bass.Path d) | P A = 0}

theorem nullSets_le_completion {d : ℕ} (P : Measure (Bass.Path d)) :
    nullSets P ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P)) :=
  MeasurableSpace.generateFrom_le fun _ hA => NullMeasurableSet.of_null hA

/-- Add all ambient null sets, and then take the right continuation. -/
noncomputable def usualFiltration {d : ℕ} (P : Measure (Bass.Path d)) :
    Filtration ℝ≥0
      (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P)) where
  seq t := ⨅ s : {s : ℝ≥0 // t < s}, Bass.rawFiltration d s.val ⊔ nullSets P
  mono' _s _t hst := le_iInf fun u => iInf_le_of_le ⟨u.val, hst.trans_lt u.property⟩ le_rfl
  le' t := iInf_le_of_le ⟨t + 1, lt_add_one t⟩
    (sup_le ((Bass.rawFiltration d).le (t + 1) |>.trans le_eventuallyMeasurableSpace)
      (nullSets_le_completion P))

instance {d : ℕ} (P : Measure (Bass.Path d)) : (usualFiltration P).IsRightContinuous := by
  constructor
  intro t
  rw [Filtration.rightCont_eq]
  change (⨅ s > t, usualFiltration P s) ≤
    ⨅ u : {u : ℝ≥0 // t < u}, Bass.rawFiltration d u.val ⊔ nullSets P
  refine le_iInf fun u => ?_
  obtain ⟨s, hts, hsu⟩ := exists_between u.property
  exact iInf₂_le_of_le s hts
    (iInf_le_of_le ⟨u.val, hsu⟩ le_rfl)

/-- Completed local martingales retain explicit integrability of every stopped process. -/
def IsLocalMartingale {d : ℕ} (M : ℝ≥0 → Bass.Path d → ℝ)
    (P : Measure (Bass.Path d)) : Prop :=
  StronglyAdapted (usualFiltration P) M ∧
    ∃ τ : ℕ → Bass.Path d → WithTop ℝ≥0,
      IsLocalizingSequence (usualFiltration P) τ P.completion ∧
        ∀ n, (∀ t, Integrable (stoppedProcess M (τ n) t) P.completion) ∧
          Martingale (stoppedProcess M (τ n)) (usualFiltration P) P.completion

/-- The all-C² martingale problem for the completed usual filtration, for the same law. -/
def SolvesMartingaleProblem {d : ℕ} (a : Vec d → Mat d) (b : Vec d → Vec d)
    (x : Vec d) (P : Measure (Bass.Path d)) : Prop :=
  IsProbabilityMeasure P ∧ (∀ᵐ γ ∂P.completion, (γ : Bass.Path d) 0 = x) ∧
    ∀ f : Vec d → ℝ, ContDiff ℝ (2 : ℕ∞) f →
      (∀ t : ℝ≥0, ∀ᵐ γ ∂P.completion,
        IntervalIntegrable (fun u : ℝ => Bass.generator a b f ((γ : Bass.Path d) u.toNNReal))
          volume 0 (t : ℝ)) ∧
      IsLocalMartingale (Bass.compensatedTest a b f) P

end EinsteinFull.External.Bass.Completion
