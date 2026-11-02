import Mathlib.MeasureTheory.Function.L2Space
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
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMCoarsenedObjects
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensitySources

/-! Vocabulary for `EinsteinFull.External.Draft.AKMCoarsenedCoefficientEstimates`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

noncomputable section

namespace EinsteinFull.External.Draft

open EinsteinRelation

open EinsteinRelation.Environment.AKMTestIntegralSupport

open EinsteinRelation.External.AKM

open EinsteinFull.External.Source.AKM

/-- A Euclidean matrix norm, equivalent to the unspecified finite-dimensional
matrix norm in AKM (5.63). Constants may depend on the dimension. -/
def coarsenedMatrixSize {d : ℕ} (M : Mat d) : ℝ :=
  Real.sqrt (∑ j : Fin d, ∑ k : Fin d, (M j k) ^ 2)

/-- The literal normalized A₁(Φ_{z,r}) flux defect in AKM (5.64).
Weighted L2 membership is explicit, so Lean's total integral cannot silently
turn a nonintegrable gradient into a normalized element. -/
def normalizedCoarseFluxDefect {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (A : Mat d) (z : Vec d) (r : ℝ) : ℝ :=
  sSup {e : ℝ | ∃ w : SubquadraticHarmonic a,
    Integrable (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ∧
    Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ≤ 1 ∧
    e = euclideanNorm
      ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
        (A + coarsenedCoefficient a A z r).mulVec
          (∫ x, heatKernel z r x • w.grad x))}

/-- DRAFT graph leaf `external:AKM#5.63-5.64`, Lemma5.24,
AKM printed p.216. This is a real spatial source statement on the source's
normalized, lattice-stationary, unit-range coefficient law. The homogenized
matrix is characterized by the source Dirichlet limit, not an arbitrary
matrix or this paper's commutator. Constants precede the law, source objects,
center and scale. The two stochastic exponents are s and s/2, respectively.
No complex force, horizontal identification or localized block estimate is
asserted. No literature axiom is admitted by this hole-free draft. -/
def akmCoarsenedCoefficientEstimatesStmt : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ K s : ℝ, 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧
    ∀ P : Measure (Coefficient d K), LawHypotheses P →
    ∀ S : SourceObjects P, ∀ (z : Vec d) (r : ℝ), 1 ≤ r →
      OsBound P (fun a => coarsenedMatrixSize
        (coarsenedCoefficient a S.homogenized z r)) s
        (C * r ^ (-(d : ℝ) / 2)) ∧
      OsBound P (fun a => normalizedCoarseFluxDefect a S.homogenized z r)
        (s / 2) (C * r ^ (-(d : ℝ)))

end EinsteinFull.External.Draft
