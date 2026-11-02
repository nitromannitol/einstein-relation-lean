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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity

/-! Vocabulary for `EinsteinFull.External.Source.AKMCoarsenedObjects`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory Filter

open scoped Topology

noncomputable section

namespace EinsteinFull.External.Source.AKM

open EinsteinRelation EinsteinRelation.External.AKM

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The source class A₁: whole-space weak a-harmonic H1_loc functions with
subquadratic normalized L2 growth, AKM (3.38), printed p.82. The gradient is
an actual weak spatial gradient; no finite test family replaces the class. -/
structure SubquadraticHarmonic {d : ℕ} {K : ℝ} (a : Coefficient d K) where
  /-- The actual whole-space weak harmonic potential. -/
  potential : Vec d → ℝ
  /-- Its weak spatial gradient, identified by `weak_gradient`. -/
  grad : Vec d → Vec d
  weak_gradient : HasWeakGradient Set.univ potential grad
  local_energy : ∀ R : ℝ, 0 < R →
    MemLp potential 2 (volume.restrict (ball 0 R)) ∧
    MemLp (fun x => euclideanNorm (grad x)) 2 (volume.restrict (ball 0 R))
  harmonic : HasWeakDivergence Set.univ (fun x => (a x).mulVec (grad x)) (fun _ => 0)
  growth : Tendsto
    (fun R : ℝ => R ^ (-2 : ℤ) * Real.sqrt (⨍ x in ball 0 R, |potential x| ^ 2))
    atTop (𝓝 0)

/-- The weighted variational energy (4.8), printed p.126. Its source uses a
nonnegative integrable unit-mass mask. This definition is total; source
theorems must retain those mask hypotheses. The supremum is over all of A₁. -/

def energyJ1 {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (mask : Vec d → ℝ) (p q : Vec d) : ℝ :=
  sSup {e : ℝ | ∃ w : SubquadraticHarmonic a,
    e = ∫ x, mask x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
      dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))}

/-- Gaussian J₁ with the source heat-kernel normalization (4.1), variance 2r². -/
def gaussianEnergyJ1 {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  energyJ1 a (heatKernel z r) p q

/-- Matrix entries of Definition5.23, (5.62), printed p.216. A is the source
homogenized matrix, to be identified in each application. The SECOND load is
A e_j in both energies. Full bilinear polarization remains an internal proof. -/
def coarsenedCoefficient {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (A : Mat d) (z : Vec d) (r : ℝ) : Mat d := fun j k =>
  (gaussianEnergyJ1 a z r (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
    gaussianEnergyJ1 a z r (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2

/-- The actual centering operation (5.86) on a selected source localization.
Existence, locality and approximation of that localization are separate inputs. -/
def centeredLocalizedEnergy {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (Jloc : Coefficient d K → Vec d → ℝ → Vec d → Vec d → ℝ)
    (a : Coefficient d K) (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  Jloc a z r p q - ∫ a', Jloc a' z r p q ∂P

end EinsteinFull.External.Source.AKM
