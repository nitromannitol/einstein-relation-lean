import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Parabolic Green-function input

Source: Armstrong–Kuusi–Mourrat (2019), Proposition E.1, printed pp. 500–501,
with (E.1)–(E.4), p. 499.
Application: `paper/main.tex:787–792,821–838,850`.

This file transcribes a literature proposition. It supplies no proof
or axiom. All spatial balls and gradient norms below are Euclidean. The
closed balls in the Lebesgue-point condition give the same averages as the
source's open balls, whose boundaries have zero Lebesgue measure.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport

/-- The Euclidean ball with arbitrary center, as used in Appendix E. -/
def heatKernelBall {d : ℕ} (x : Vec d) (r : ℝ) : Set (Vec d) :=
  {z | euclideanNorm (z - x) < r}

/-- The normalized Lebesgue-point condition in Proposition E.1, p. 501. -/
def IsHeatKernelLebesguePoint {d : ℕ} (f : Vec d → ℝ) (y : Vec d) : Prop :=
  Tendsto (fun r : ℝ =>
    ⨍ z in Metric.closedBall (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) r,
      |f (WithLp.ofLp z) - f y| ∂volume)
    (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)

/-- Energy solutions of (E.1) or (E.2) with initial unit point mass.
The initial condition is tested against actual compact smooth functions. -/
def IsFundamentalSolution {d : ℕ} {K : ℝ} (A : Coefficient d K)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) : Prop :=
  (∀ (a b R : ℝ), 0 < a → a < b → 0 < R →
    IsParabolicSolution A (Set.Ioo a b) (originBall d R) u G) ∧
  ∀ ψ : Vec d → ℝ, IsSpatialTest Set.univ ψ →
    Tendsto (fun t => ∫ x, u (t, x) * ψ x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (ψ y))

/-- The mixed weak derivative in (E.9). Both derivatives act in space;
the test is supported at positive times. -/
def IsHeatKernelMixedDerivative {d : ℕ}
    (P : ℝ → Vec d → Vec d → ℝ)
    (H : ℝ → Vec d → Vec d → Mat d) : Prop :=
  (∀ i j, LocallyIntegrableOn
    (fun z : ℝ × (Vec d × Vec d) => H z.1 z.2.1 z.2.2 i j)
    (Set.Ioi 0 ×ˢ Set.univ) volume) ∧
  ∀ ψ : ℝ × (Vec d × Vec d) → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Set.Ioi 0 ×ˢ Set.univ → ∀ i j,
    (∫ z : ℝ × (Vec d × Vec d), P z.1 z.2.1 z.2.2 *
      fderiv ℝ (fun w => fderiv ℝ ψ w (0, (0, unitVector j))) z
        (0, (unitVector i, 0))) =
      ∫ z : ℝ × (Vec d × Vec d), H z.1 z.2.1 z.2.2 i j * ψ z

/-- The conclusions of Proposition E.1 for one coefficient and its kernel.
`X`, `Y`, and `H` are the weak derivatives in x, y, and x,y. The same
function `C` works in (E.7)–(E.9). No stationarity or finite range is used. -/
def HeatKernelProperties {d : ℕ} {K : ℝ} (A : Coefficient d K)
    (P : ℝ → Vec d → Vec d → ℝ)
    (X Y : ℝ → Vec d → Vec d → Vec d)
    (H : ℝ → Vec d → Vec d → Mat d) (C : ℝ → ℝ) : Prop :=
  ContinuousOn (fun z : ℝ × (Vec d × Vec d) => P z.1 z.2.1 z.2.2)
    (Set.Ioi 0 ×ˢ Set.univ) ∧
  (∀ t, 0 < t → ∀ x y, 0 ≤ P t x y) ∧
  (∀ y, IsFundamentalSolution A y (fun z => P z.1 z.2 y) (fun z => X z.1 z.2 y)) ∧
  (∀ x, IsFundamentalSolution A x (fun z => P z.1 x z.2) (fun z => Y z.1 x z.2)) ∧
  (∀ t, 0 < t → ∀ x y, P t x y = P t y x) ∧
  (∀ t, 0 < t → ∀ x,
    Integrable (P t x) volume ∧ (∫ y, P t x y ∂volume) = 1 ∧
    Integrable (fun y => P t y x) volume ∧ (∫ y, P t y x ∂volume) = 1) ∧
  IsHeatKernelMixedDerivative P H ∧
  (∀ α : ℝ, 0 < α → α < K⁻¹ → ∀ t : ℝ, 0 < t → ∀ x y : Vec d,
    |P t x y| ≤ C α * t ^ (-(d : ℝ) / 2) *
      Real.exp (-α * euclideanSq (x - y) / (4 * t)) ∧
    (∀ r : ℝ, 0 < r → r ≤ Real.sqrt t / 2 →
      r * (vectorRms volume (Set.Ioo (t-r^2) t ×ˢ heatKernelBall x r)
        (fun z => X z.1 z.2 y) +
        vectorRms volume (Set.Ioo (t-r^2) t ×ˢ heatKernelBall y r)
        (fun z => Y z.1 x z.2)) ≤
      C α * t ^ (-(d : ℝ) / 2) * Real.exp (-α * euclideanSq (x-y) / (4*t))) ∧
    (∀ r : ℝ, 0 < r → r ≤ Real.sqrt t / 2 →
      IntegrableOn
        (fun z : ℝ × (Vec d × Vec d) =>
          ∑ i : Fin d, ∑ j : Fin d, (H z.1 z.2.1 z.2.2 i j)^2)
        (Set.Ioo (t-r^2) t ×ˢ
          (heatKernelBall x r ×ˢ heatKernelBall y r)) volume ∧
      r^2 * Real.sqrt (⨍ z in
        Set.Ioo (t-r^2) t ×ˢ (heatKernelBall x r ×ˢ heatKernelBall y r),
          ∑ i : Fin d, ∑ j : Fin d, (H z.1 z.2.1 z.2.2 i j)^2 ∂volume) ≤
      C α * t ^ (-(d : ℝ) / 2) * Real.exp (-α * euclideanSq (x-y) / (4*t)))) ∧
  (∀ (f : Vec d → ℝ), LocallyIntegrable f volume → ∀ y : Vec d,
    (∃ k : ℝ, 0 ≤ k ∧
      Integrable (fun x => |f x| * Real.exp (-k * euclideanSq (x-y))) volume) →
    IsHeatKernelLebesguePoint f y →
    Tendsto (fun t => ∫ x, P t x y * f x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (f y)))

/-- Transcription of AKM Proposition E.1, printed pp. 500–501.
The only coefficient hypotheses are (0.6) and symmetry, contained in
`Coefficient`. Constants depend on α, d, K, and precede the coefficient. -/
def ParabolicHeatKernel : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ K : ℝ, 1 < K →
    ∃ C : ℝ → ℝ, (∀ α, 0 < α → α < K⁻¹ → 0 < C α) ∧
      ∀ A : Coefficient d K,
        ∃ (P : ℝ → Vec d → Vec d → ℝ)
          (X Y : ℝ → Vec d → Vec d → Vec d)
          (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A P X Y H C

end EinsteinRelation.External.AKM
