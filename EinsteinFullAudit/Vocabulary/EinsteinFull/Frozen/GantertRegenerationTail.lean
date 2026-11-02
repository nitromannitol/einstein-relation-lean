import Mathlib.Analysis.SpecialFunctions.Exp
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
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.RegenerationNoReturn
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.RegenerationTime
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

/-! Vocabulary for `EinsteinFull.Frozen.GantertRegenerationTail`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

open scoped NNReal ENNReal

namespace EinsteinFull.External

open EinsteinRelation

/-- GMP Lemma 5.8, (5.22), and the no-return bound (5.20), for the
Section 7 zero-potential diffusion with the actual split coupling.
Literature assumption restricted to the literal cited tail and no-return facts.
No factorization, multi-cycle moment or lattice-renewal conclusion is assumed. -/
axiom gantert_regeneration_tail (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K →
      ENNReal.ofReal (1 / 2 : ℝ) ≤
        Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ∧
      ∀ t : ℝ, 0 ≤ t →
        Regeneration.annealedCoupledLaw Q.measure K
          {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
            ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))

end EinsteinFull.External
