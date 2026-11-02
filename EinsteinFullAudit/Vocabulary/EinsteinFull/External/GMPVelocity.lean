import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Topology.List
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Draft.GMPVelocity
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

/-! Vocabulary for `EinsteinFull.External.GMPVelocity`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull.External

/-- Reviewed GMP positive small-force quenched velocity law and strict positive
force projection, for the source physical origin process. This exact source
alias retains translation ergodicity and the source force range. The internal
regeneration ratio and signed/reduced-process transfers are not inputs.
Direct-PDF evidence: literature-gmp-velocity-v1. -/
axiom gmp_velocity : EinsteinFull.External.Draft.gmpVelocityStmt

end EinsteinFull.External
