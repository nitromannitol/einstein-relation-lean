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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.MatrixNorm
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity

/-! Vocabulary for `EinsteinRelation.External.AKMCorrectorOscillation`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

open scoped Topology

noncomputable section

namespace EinsteinRelation.External.AKM

open Environment.AKMTestIntegralSupport

/-- AKM Appendix A's stochastic bound for an almost-everywhere measurable
representative. Corrector potentials are specified only almost surely, so
their stochastic estimates must be unchanged by null-set modifications. -/
def AEOsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  AEMeasurable X P ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2

/-- Convolution against AKM's standard Euclidean heat kernel, (4.1). -/
def scalarHeatAverage {d : ℕ} (u : Vec d → ℝ) (x : Vec d) (r : ℝ) : ℝ :=
  ∫ z, heatKernel x r z * u z ∂volume

/-- Lattice stationarity of the values of a scalar random field. -/
def ScalarStationary {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (u : Coefficient d K → Vec d → ℝ) : Prop :=
  ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
    u a (x + latticeShift z) = u (translateCoefficient (latticeShift z) a) x

/-- The local L² interpretation of the iterated positive-time integral
(6.7). Space is integrated first; the two time endpoints vary independently.
The integrability clauses ensure that both integrals are genuine integrals. -/
def IsHeatSelectedFluxGradient {d : ℕ} (g : Vec d → Vec d)
    (G : Fin d → Fin d → Vec d → Vec d) : Prop :=
  ∀ j k ℓ : Fin d, ∀ R : ℕ,
    let μ : Measure (Vec d) := volume.restrict (ball 0 (R + 1))
    (∀ m n : ℕ, ∀ᵐ x ∂μ,
      (∀ᵐ t ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
        Integrable (fun y =>
          Correctors.HeatSelectedSkewMeaning.akmHeatGradientDensity g t j k ℓ x y)
          volume) ∧
      Integrable (fun t =>
        Correctors.HeatSelectedSkewMeaning.akmHeatGradientSpaceIntegral g t j k ℓ x)
        (volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)))) ∧
    (∀ m n : ℕ, MemLp
      (fun x => Correctors.HeatSelectedSkewMeaning.iteratedAKMHeatGradientTruncation
        g m n j k ℓ x) 2 μ) ∧
    MemLp (fun x => G j k x ℓ) 2 μ ∧
    Filter.Tendsto (fun mn : ℕ × ℕ => eLpNorm
      (fun x => Correctors.HeatSelectedSkewMeaning.iteratedAKMHeatGradientTruncation
        g mn.1 mn.2 j k ℓ x - G j k x ℓ) 2 μ) Filter.atTop (nhds 0)

end EinsteinRelation.External.AKM
