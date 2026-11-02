import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Topology.List
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.MeanValue
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.EnvironmentLaw
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.RegenerationCoupling
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.WeightedFormIntegrabilitySupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.WeightedH1QuotientSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.GMPFamily
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.GantertSection7Support
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Probability.ProbabilityPart
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Regeneration.Construction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Regeneration.Coupling
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Regeneration.RenewalCarriers

/-! Vocabulary for `EinsteinFull.Frozen.RegenerationNoReturn`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull

open EinsteinRelation

/-- The actual no-return event D, relative to the initial point. -/
def regenerationNoReturn {d : ℕ} (hd : 2 ≤ d) (R : ℝ) :
    Set (FieldPair d × Regeneration.CoupledSample d) :=
  {ωz | Regeneration.NoBacktracking R ωz.2.1 (Regeneration.Renewal.forceCoord hd)}

end EinsteinFull
