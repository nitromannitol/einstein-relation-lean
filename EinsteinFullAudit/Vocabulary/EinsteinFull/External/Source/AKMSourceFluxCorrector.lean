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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMCorrectorOscillation
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensitySources

/-! Vocabulary for `EinsteinFull.External.Source.AKMSourceFluxCorrector`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

noncomputable section

namespace EinsteinFull.External.Source.AKM

open EinsteinRelation EinsteinRelation.External.AKM

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The literal source mean cell flux. This total integral imposes no
integrability premise on the corrector. Its integrability and identification
with the homogenized flux must be derived separately. -/
def sourceMeanFlux {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)} {e : Vec d}
    (φ : SourceCorrector P e) : Vec d :=
  ∫ a, ∫ x in unitCell d, (a x).mulVec (e + φ.grad a x) ∂volume ∂P

/-- The source flux in (6.7). The spatial Gaussian Hessian annihilates the
constant centering vector. No cell integrability or expected-flux equality
is a hypothesis of this definition or the heat-selected carrier below. -/
def sourceCenteredFlux {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : SourceCorrector P e) (a : Coefficient d K) (x : Vec d) : Vec d :=
  (a x).mulVec (e + φ.grad a x) - sourceMeanFlux φ

/-- The source flux potential selected up to constants by AKM (6.7), printed
p.246. This is the existing literal heat selection, weak gradient and local
Sobolev carrier retyped over `SourceCorrector`; it assumes no quantitative
bound or derived annealed cell-flux integrability. -/
structure SourceFluxCorrector {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : SourceCorrector P e) where
  /-- The spatial matrix-valued flux potential, defined up to constants. -/
  potential : Coefficient d K → Vec d → Mat d
  /-- The weak spatial gradient of each matrix entry. -/
  grad : Coefficient d K → Fin d → Fin d → Vec d → Vec d
  measurable_potential : Measurable
    (fun p : Coefficient d K × Vec d => potential p.1 p.2)
  measurable_grad : ∀ j k, Measurable
    (fun p : Coefficient d K × Vec d => grad p.1 j k p.2)
  weak_gradient : ∀ᵐ a ∂P, ∀ j k,
    HasWeakGradient Set.univ (fun x => potential a x j k) (grad a j k)
  locally_square_integrable : ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R → ∀ j k,
    MemLp (fun x => potential a x j k) 2 (volume.restrict (ball 0 R)) ∧
    MemLp (grad a j k) 2 (volume.restrict (ball 0 R))
  heat_selected : ∀ᵐ a ∂P, IsHeatSelectedFluxGradient (sourceCenteredFlux φ a) (grad a)

end EinsteinFull.External.Source.AKM
