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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinRelation.External.AKMEnergyDensity`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace EinsteinRelation.External.AKM

open Environment.AKMTestIntegralSupport

/-- The open Euclidean ball in the coordinate carrier. -/
def ball {d : ℕ} (x : Vec d) (r : ℝ) : Set (Vec d) :=
  {y | euclideanNorm (y - x) < r}

/-- The centered unit cell; its boundary has Lebesgue measure zero. -/
def unitCell (d : ℕ) : Set (Vec d) := Set.pi Set.univ (fun _ => Set.Ico (-1 / 2) (1 / 2))

/-- AKM (0.10)--(0.11), pp. xvii--xviii. Normalized symmetric ellipticity
(0.6) is built into `Coefficient`; no full real-translation stationarity is assumed. -/
def LawHypotheses {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K)) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P) ∧
  AKMFiniteRange P

/-- AKM's kernel `Φ_{x,r}(y) = Φ(r²,y-x)`, (4.1), p. 124.
It is the kernel of `exp(t Δ)`, with variance `2t` in each coordinate. -/
def heatKernel {d : ℕ} (x : Vec d) (r : ℝ) (y : Vec d) : ℝ :=
  Correctors.euclideanHeatKernel (r ^ 2) (y - x)

/-- AKM Appendix A, (A.1)--(A.2), p. 455. Positivity of `s, θ` is explicit;
`X₊ = max X 0`. This notation itself supplies no stochastic estimate. -/
def OsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  Measurable X ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2

end EinsteinRelation.External.AKM
