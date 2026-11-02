import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import EinsteinRelation.Calculus.Generator
import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport

/-!
# Heat-selected skew corrector meaning

This module records the Euclidean heat formula, its iterated local `L²`
selection predicate, and the source identities for a skew flux-corrector
column. The source conventions are anchored at `paper/main.tex`,
lines 688–702, 732–735, 748, and 754–758. The heat formula follows AKM,
equation (6.7); local `L²` convergence is recorded by the selection
predicate below.
-/


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

private def iteratedHeatTimeWindowForMeaning (m n : ℕ) : Set ℝ :=
  Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)

/-- The source iterated heat formula selects a local spatial `L²` gradient.
For each positive-time truncation, its full-space inner integral and outer
time integral are genuine integrals. The two time endpoints tend independently
to zero and infinity, and the resulting functions converge locally in `L²`. -/
def IsIteratedAKMHeatGradientAt {d : ℕ} (g : Vec d → Vec d)
    (ρ : FieldPair d)
    (F : FieldPair d → Fin d → Fin d → Fin d → ℝ) : Prop :=
  ∀ row col k : Fin d, ∀ R : ℕ,
    let μ : Measure (Vec d) :=
      volume.restrict (Metric.ball (0 : Vec d) ((R + 1 : ℕ) : ℝ))
    (∀ m n : ℕ,
      ∀ᵐ x ∂μ,
        (∀ᵐ t ∂(volume.restrict (iteratedHeatTimeWindowForMeaning m n)),
          Integrable
            (fun y : Vec d => akmHeatGradientDensity g t row col k x y)
            volume) ∧
        Integrable
          (fun t : ℝ => akmHeatGradientSpaceIntegral g t row col k x)
          (volume.restrict (iteratedHeatTimeWindowForMeaning m n))) ∧
    (∀ m n : ℕ,
      MemLp
        (fun x : Vec d => iteratedAKMHeatGradientTruncation g m n row col k x)
        2 μ) ∧
    MemLp (fun x : Vec d => F (translate x ρ) row col k) 2 μ ∧
    Filter.Tendsto
      (fun mn : ℕ × ℕ =>
        eLpNorm
          (fun x : Vec d =>
            iteratedAKMHeatGradientTruncation g mn.1 mn.2 row col k x -
              F (translate x ρ) row col k)
          2 μ)
      Filter.atTop (nhds (0 : ENNReal))

/-- The manuscript's skewness, row-divergence, and Poisson identities for one
sample, using its row-first matrix indexing and displayed signs. -/
def HasSourceSkewCorrectorColumnAt {d : ℕ} (_hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (σ : FieldPair d → Vec d → Mat d) (ρ : FieldPair d) : Prop :=
  let dCoord : (Vec d → ℝ) → Fin d → Vec d → ℝ := fun f j x =>
    coordinateDerivative j f x
  let laplacian : (Vec d → ℝ) → Vec d → ℝ := fun f x =>
    ∑ ℓ : Fin d, dCoord (dCoord f ℓ) ℓ x
  let g : Vec d → Vec d := fun x =>
    (canonicalCorrectorFlux Q i (translate x ρ) -
      expectedCorrectorFlux Q i).ofLp
  (∀ᵐ x ∂volume, (σ ρ x).transpose = -(σ ρ x)) ∧
  (∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∀ j : Fin d,
      Integrable (fun x : Vec d => g x j * ψ x) volume ∧
      Integrable (fun x : Vec d =>
        ∑ k : Fin d, σ ρ x j k * dCoord ψ k x) volume ∧
      (∫ x : Vec d, g x j * ψ x ∂volume) =
        -(∫ x : Vec d, ∑ k : Fin d, σ ρ x j k * dCoord ψ k x ∂volume)) ∧
  (∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∀ j k : Fin d,
      Integrable (fun x : Vec d => σ ρ x j k * (-laplacian ψ x)) volume ∧
      Integrable (fun x : Vec d => g x k * dCoord ψ j x) volume ∧
      Integrable (fun x : Vec d => g x j * dCoord ψ k x) volume ∧
      (∫ x : Vec d, σ ρ x j k * (-laplacian ψ x) ∂volume) =
        -(∫ x : Vec d, g x k * dCoord ψ j x ∂volume) +
          ∫ x : Vec d, g x j * dCoord ψ k x ∂volume)

/-- The heat-selected object is a weak gradient of a skew potential; only this
gradient is fixed here, leaving value normalization to the source's separate
`ζ_R` centering. -/
def HasSelectedHeatGradientRepresentative {d : ℕ}
    (σ : Vec d → Mat d)
    (F : FieldPair d → Fin d → Fin d → Fin d → ℝ)
    (ρ : FieldPair d) : Prop :=
  ∀ row col : Fin d,
    HasWeakGradient Set.univ (fun x => σ x row col)
      (fun x k => F (translate x ρ) row col k)

/-- A source skew-corrector column whose stationary gradient is selected by
the literal iterated AKM heat formula for the canonical centered flux. -/
def HasHeatSelectedSkewCorrectorColumn {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (σ : FieldPair d → Vec d → Mat d) : Prop :=
  ∃ F : FieldPair d → Fin d → Fin d → Fin d → ℝ,
    (∀ row col k : Fin d,
      AEStronglyMeasurable (fun ρ => F ρ row col k) (reducedEnvironmentLaw Q)) ∧
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
      HasSourceSkewCorrectorColumnAt hd Q i σ ρ ∧
      IsIteratedAKMHeatGradientAt
        (fun x : Vec d =>
          (canonicalCorrectorFlux Q i (translate x ρ) -
            expectedCorrectorFlux Q i).ofLp)
        ρ F ∧
      HasSelectedHeatGradientRepresentative (σ ρ) F ρ

end EinsteinRelation.Correctors.HeatSelectedSkewMeaning
