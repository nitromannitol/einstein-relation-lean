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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMLocalCorrectors

/-! Vocabulary for `EinsteinFull.External.Source.AKMLocalizedEnergy`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

noncomputable section

namespace EinsteinFull.External.Source.AKM

open EinsteinRelation EinsteinRelation.External.AKM

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The exponent ε immediately following AKM (4.85). -/
def localizationEpsilon (δ α γ : ℝ) : ℝ :=
  min ((α * (1 + δ) + δ - γ) / (1 + α)) (δ / 2)

/-- The containing radius T=r^(1+δ), AKM p.155. -/
def localizationOuterRadius (δ r : ℝ) : ℝ := r ^ (1 + δ)

/-- The intermediate radius S=r^(1+δ−ε), AKM p.155. -/
def localizationIntermediateRadius (δ α γ r : ℝ) : ℝ :=
  r ^ (1 + δ - localizationEpsilon δ α γ)

/-- Actual finite-domain H¹ weak a-harmonic functions A(B_T(z)). Values
outside the domain are immaterial to every functional below. In particular,
these functions need not be whole-space subquadratic harmonic functions. -/
structure LocalHarmonic {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (z : Vec d) (T : ℝ) where
  /-- Potential on the source ball. -/
  potential : Vec d → ℝ
  /-- Its actual weak Euclidean gradient on that ball. -/
  grad : Vec d → Vec d
  square_integrable : MemLp potential 2 (volume.restrict (ball z T))
  gradient_square_integrable :
    MemLp (fun x => euclideanNorm (grad x)) 2 (volume.restrict (ball z T))
  weak_gradient : HasWeakGradient (ball z T) potential grad
  harmonic :
    HasWeakDivergence (ball z T) (fun x => (a x).mulVec (grad x)) (fun _ => 0)

/-- The admissible convex class K on p.155: the normalized gradient L²
norm is at most C. The constant is a structural choice in source theorems. -/
def IsLocalizationAdmissible {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T : ℝ} (C : ℝ) (w : LocalHarmonic a z T) : Prop :=
  vectorRms volume (ball z T) w.grad ≤ C

/-- The objective I on p.155. The OUTER integral is a volume average;
the inner Gaussian convolution is not renormalized after truncation. -/
def localizationObjective {d : ℕ} (z : Vec d) (T S σ θ : ℝ)
    (w : Vec d → ℝ) : ℝ :=
  ⨍ y in ball z (S / θ), (∫ x in ball z T, heatKernel y (σ * S) x * w x) ^ 2

/-- The literal coordinate minimization on p.155. Coordinates are taken
relative to the center, translating the source's ℓ_{e_i}(x)=x_i at z=0. -/
def IsCoordinateMinimizer {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T : ℝ} (S σ θ C : ℝ) (i : Fin d)
    (w : LocalHarmonic a z T) : Prop :=
  IsLocalizationAdmissible C w ∧
    ∀ v : LocalHarmonic a z T, IsLocalizationAdmissible C v →
      localizationObjective z T S σ θ (fun x => w.potential x - (x - z) i) ≤
        localizationObjective z T S σ θ (fun x => v.potential x - (x - z) i)

/-- The source's permissible tie-break on p.156: among actual minimizers,
choose a representative with smallest L²(B_T) norm. No existence is assumed. -/
def IsLeastNormCoordinateMinimizer {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T : ℝ} (S σ θ C : ℝ) (i : Fin d)
    (w : LocalHarmonic a z T) : Prop :=
  IsCoordinateMinimizer S σ θ C i w ∧
    ∀ v : LocalHarmonic a z T, IsCoordinateMinimizer S σ θ C i v →
      (∫ x in ball z T, w.potential x ^ 2) ≤
        ∫ x in ball z T, v.potential x ^ 2

/-- The d genuine selected coordinate minimizers defining V_r^δ on p.156.
This carrier records only the source minimization, without locality,
measurability, linear independence, estimates or a homogenized coefficient. -/
structure LocalizedBasis {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (z : Vec d) (T S σ θ C : ℝ) where
  /-- The source coordinate potentials and their weak gradients. -/
  coordinate : Fin d → LocalHarmonic a z T
  /-- Exact variational selection, including the stated least-norm tie-break. -/
  selected : ∀ i, IsLeastNormCoordinateMinimizer S σ θ C i (coordinate i)

/-- The corresponding linear combination of the actual weak gradients. -/
def localizedGradient {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (c : Vec d) (x : Vec d) : Vec d :=
  ∑ i, c i • (W.coordinate i).grad x

/-- The energy in (4.103), now over the actual selected finite-dimensional
space. Its supremum is over every real linear combination of the d selected
potentials. It is not an affine-Dirichlet energy or a smoothed commutator. -/
def localizedEnergyJ1 {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (r : ℝ) (p q : Vec d) : ℝ :=
  sSup {e : ℝ | ∃ c : Vec d,
    e = ∫ x in ball z T, heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (localizedGradient W c x)
          ((a x).mulVec (localizedGradient W c x)) -
        dot p ((a x).mulVec (localizedGradient W c x)) +
          dot q (localizedGradient W c x))}

end EinsteinFull.External.Source.AKM
