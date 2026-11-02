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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity

/-! Vocabulary for `EinsteinRelation.External.AKMEnergyDensitySources`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory Filter Topology

noncomputable section

namespace EinsteinRelation.External.AKM

open Environment.AKMTestIntegralSupport

/-- The open triadic cube of AKM (0.20), used in (1.22). -/
def sourceTriadicCube (d n : ℕ) : Set (Vec d) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-((3 : ℝ) ^ n) / 2) (((3 : ℝ) ^ n) / 2))

/-- A zero-boundary Sobolev function together with its actual weak gradient.
The closure of smooth compactly supported functions is taken simultaneously
in the scalar and gradient L² norms, the definition of `H¹₀(U)` used in
AKM (1.7), printed p. 5. -/
def SourceH01 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ)
    (g : Vec d → Vec d) : Prop :=
  MemLp u 2 (volume.restrict U) ∧ MemLp g 2 (volume.restrict U) ∧
    HasWeakGradient U u g ∧
    ∃ v : ℕ → Vec d → ℝ, (∀ n, IsSpatialTest U (v n)) ∧
      Tendsto (fun n => ∫ x in U, (v n x - u x)^2 ∂volume) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in U,
        euclideanSq (gradient (v n) x - g x) ∂volume) atTop (𝓝 0)

/-- The Dirichlet energy minimum `μ(U,e)`, AKM (1.7), p. 5.
The admissible potentials are `e·x + u` with `u ∈ H¹₀(U)`. -/
def sourceDirichletEnergy {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Set (Vec d)) (e : Vec d) : ℝ :=
  sInf {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), SourceH01 U u g ∧
    E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume}

/-- The source first-order corrector characterization. Definitions 3.14--3.15,
Lemma 3.16 and its proof, pp. 98--100: a stationary local H¹ potential
gradient, affine harmonicity and centered sublinear L² oscillation.
No cell-flux integrability or mean-flux formula is a defining property. -/
structure SourceCorrector {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (e : Vec d) where
  potential : Coefficient d K → Vec d → ℝ
  grad : Coefficient d K → Vec d → Vec d
  measurable_grad : Measurable (fun p : Coefficient d K × Vec d => grad p.1 p.2)
  weak_gradient : ∀ᵐ a ∂P, HasWeakGradient Set.univ (potential a) (grad a)
  locally_square_integrable : ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R →
    MemLp (potential a) 2 (volume.restrict (ball 0 R)) ∧
    MemLp (grad a) 2 (volume.restrict (ball 0 R))
  stationary : ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
    grad a (x + latticeShift z) = grad (translateCoefficient (latticeShift z) a) x
  harmonic : ∀ᵐ a ∂P,
    HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + grad a x)) (fun _ => 0)
  sublinear : ∀ᵐ a ∂P, Tendsto
    (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (potential a x - ⨍ y in ball 0 R, potential a y ∂volume)^2 ∂volume))
    atTop (𝓝 0)

/-- The characterized objects used in AKM (4.4) and (3.93).
The matrix characterization is the symmetric quadratic-form identity of
Definition 1.2 with the limit (1.22), rather than a corrector-flux formula. -/
structure SourceObjects {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K)) where
  corrector : ∀ e : Vec d, SourceCorrector P e
  homogenized : Mat d
  symmetric : homogenized.transpose = homogenized
  variational_limit : ∀ e : Vec d,
    Tendsto (fun n : ℕ => ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P)
      atTop (𝓝 ((1 / 2 : ℝ) * dot e (homogenized.mulVec e)))

/-- The literal Gaussian-weighted scalar energy of a source corrector. -/
def sourceEnergyAverage {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : SourceCorrector P e) (x : Vec d) (r : ℝ)
    (a : Coefficient d K) : ℝ :=
  ∫ y, heatKernel x r y *
    ((1 / 2 : ℝ) * dot (e + φ.grad a y) ((a y).mulVec (e + φ.grad a y))) ∂volume

end EinsteinRelation.External.AKM
