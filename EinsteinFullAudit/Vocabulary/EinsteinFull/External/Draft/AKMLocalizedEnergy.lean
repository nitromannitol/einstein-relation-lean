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
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMCoarsenedObjects
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMLocalCorrectors

/-! Vocabulary for `EinsteinFull.External.Draft.AKMLocalizedEnergy`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

namespace EinsteinFull.External.Draft

open EinsteinRelation EinsteinRelation.External.AKM

open EinsteinRelation.Environment.AKMTestIntegralSupport

open EinsteinFull.External.Source.AKM

/-- DRAFT graph leaf `external:AKM#5.85`, AKM printed pp.221–222,
with the actual coordinate minimization of pp.155–156 and energy (4.103).
The source constants are chosen before the law. The exponent called α in
(5.82) is γ here; α below is the auxiliary fluctuation exponent in (4.84).
Only r≥2 is retained, the domain of the explicit source construction.
The conclusion supplies genuine minimizing selectors and the source local
sigma algebra, not an arbitrary localized energy with presumed estimates.
No stationary-carrier, complex-force or commutator identification is asserted. -/
def akmLocalizedEnergyStmt : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ K s δ γ : ℝ,
    1 < K → 1 < s → s < 2 → 0 < δ →
    (d : ℝ) / 2 * (1 + δ) < γ →
    γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
    ∃ α σ θ C₀ C : ℝ,
      0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
      0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧ 0 < C ∧
      ∀ P : Measure (Coefficient d K), LawHypotheses P →
      ∃ W : ∀ (a : Coefficient d K) (z : Vec d) (r : ℝ), 2 ≤ r →
          LocalizedBasis a z (localizationOuterRadius δ r)
            (localizationIntermediateRadius δ α γ r) σ θ C₀,
        ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
          euclideanNorm p < 1 → euclideanNorm q < 1 →
          @Measurable (Coefficient d K) ℝ
            (localSigma (ball z (localizationOuterRadius δ r))) inferInstance
            (fun a => localizedEnergyJ1 (W a z r hr) r p q) ∧
          OsBound P (fun a =>
            |gaussianEnergyJ1 a z r p q - localizedEnergyJ1 (W a z r hr) r p q|)
            s (C * r ^ (-γ))

end EinsteinFull.External.Draft
