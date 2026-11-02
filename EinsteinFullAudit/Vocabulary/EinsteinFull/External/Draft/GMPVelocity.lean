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

/-! Vocabulary for `EinsteinFull.External.Draft.GMPVelocity`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull.External.Draft

open EinsteinRelation

open EinsteinRelation.External.GantertSection7Support

/-- DRAFT graph leaf `external:GMP#5.9`: the fixed positive-force law of large
numbers of Proposition 5.9, printed p.27, and the strict longitudinal positivity
stated in Section 2.3, printed p.5. Section 7, printed p.32, extends this law to
its actual weak-operator process. Translation ergodicity is explicit. The
source force range is retained. This statement concerns the physical source
origin law only: reduced coefficients, signed/arbitrary forces, martingale-law
identification and the regeneration-ratio application remain internal. -/
def gmpVelocityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R),
    IsTranslationErgodic Q.measure →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)),
      IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
        0 < v (firstCoordinateIndex hd)

end EinsteinFull.External.Draft
