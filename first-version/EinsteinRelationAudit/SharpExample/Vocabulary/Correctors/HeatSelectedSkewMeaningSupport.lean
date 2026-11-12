import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.Generator
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.Weak
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.CanonicalVariationalGradientSupport

/-! Restated from the library module `EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation.Correctors.HeatSelectedSkewMeaning
noncomputable def gaussianHeatKernel {d : ℕ} (t : ℝ) (_ht : 0 < t)
    (z : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
    Real.exp (-euclideanSq z / (4 * t))
noncomputable def centeredGaussianHeatKernel {d : ℕ} (t : ℝ) (ht : 0 < t)
    (y x : Vec d) : ℝ :=
  gaussianHeatKernel t ht (y - x)
noncomputable def centeredGaussianHeatKernelSecondDerivative {d : ℕ}
    (t : ℝ) (ht : 0 < t) (y x : Vec d) (i k : Fin d) : ℝ :=
  coordinateDerivative k
    (fun z => coordinateDerivative i
      (fun w => centeredGaussianHeatKernel t ht y w) z) x
/-- The `k` component of the row/column ordered AKM (6.7) integrand. -/
noncomputable def akmHeatGradientDensity {d : ℕ} (g : Vec d → Vec d)
    (t : ℝ) (row col k : Fin d) (x y : Vec d) : ℝ :=
  if ht : 0 < t then
    g y col * centeredGaussianHeatKernelSecondDerivative t ht y x row k -
      g y row * centeredGaussianHeatKernelSecondDerivative t ht y x col k
  else 0
/-- The full-space spatial integral in AKM (6.7), before the positive-time
integration is performed. -/
noncomputable def akmHeatGradientSpaceIntegral {d : ℕ}
    (g : Vec d → Vec d) (t : ℝ) (row col k : Fin d) (x : Vec d) : ℝ :=
  ∫ y : Vec d, akmHeatGradientDensity g t row col k x y
def iteratedHeatTimeWindow (m n : ℕ) : Set ℝ :=
  Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)
/-- The AKM (6.7) heat-gradient formula in its source order: the full-space
integral in `y` is evaluated at each time before integration in positive time.
The independent cutoffs approximate the two time endpoints without truncating
the spatial integral. -/
noncomputable def iteratedAKMHeatGradientTruncation {d : ℕ}
    (g : Vec d → Vec d) (m n : ℕ) (row col k : Fin d) (x : Vec d) : ℝ :=
  ∫ t in iteratedHeatTimeWindow m n,
    akmHeatGradientSpaceIntegral g t row col k x
end EinsteinRelation.Correctors.HeatSelectedSkewMeaning
