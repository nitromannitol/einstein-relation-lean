import EinsteinRelation.Diffusion.Basic

/-!
# Draft literature input: well-posedness of the martingale problem

DRAFT, statement only (a hole-free `Prop`, not an axiom, not imported by `EinsteinFull.lean`).
It is admitted only after direct review against the printed source.

Source to be transcribed: D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion
Processes*, Grundlehren 233, Springer 1979, Theorem 7.2.1 (uniqueness, for a bounded continuous
diffusion matrix, bounded measurable drift) together with the existence results of Chapter 6
(bounded continuous `a`, bounded measurable `b`; theorem number to be recorded); alternatively
R. F. Bass, *Diffusions and Elliptic Operators*, Springer 1998, the well-posedness theorem for
continuous uniformly elliptic `a` and bounded measurable `b` (Chapter 6/7).

The PDF of neither source is in `paper/References`: the exact theorem numbers, the exact
hypotheses (positive definiteness versus uniform ellipticity, time dependence of the
coefficients, test-function class) and the notion of solution MUST be compared with the printed
text before admission. This draft is written with the strongest hypotheses that any of the two
sources could require, and it states only a time-homogeneous special case (`a`, `b` independent
of time, start at time `0`), so that a correct comparison can only weaken what is needed.

Choices made here, each to be checked against the text:
* path space `C([0,∞), ℝᵈ)` with the Borel σ-algebra (equal to the coordinate σ-algebra) and the
  canonical (natural) filtration of the coordinate process (`pathFiltration`);
* generator `L f = ½ Σᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ f + Σᵢ bᵢ ∂ᵢ f` on `C_c^∞(ℝᵈ)`; the second derivatives are
  the iterated coordinate Fréchet derivatives, which are the classical derivatives of `f`;
* a solution from `x` is a probability measure `P` on path space with `P (γ 0 = x) = 1` such
  that `f (γ t) - f (γ 0) - ∫₀ᵗ L f (γ u) du` is a `P`-martingale for the canonical filtration
  for all test functions `f ∈ C_c^∞` (the integrability clauses of `SolvesMartingaleProblem`
  are automatic for bounded `a`, `b`, since then `L f` is bounded and Borel);
* `a` symmetric, continuous, entrywise bounded, uniformly positive definite in the Euclidean
  quadratic form; `b` Borel and entrywise bounded;
* conclusion: for every start there is exactly one solution. Measurability of `x ↦ Pₓ` is NOT
  part of the statement (it is proved internally from uniqueness).
-/

open MeasureTheory

namespace EinsteinFull.External.Draft
open EinsteinRelation

/-- The differential operator `½ Σᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ f + Σᵢ bᵢ ∂ᵢ f` of a diffusion matrix `a` and a
drift `b`, with iterated coordinate Fréchet derivatives. -/
noncomputable def svGenerator {d : ℕ} (a : Vec d → Mat d) (b : Vec d → Vec d)
    (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j *
      fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) +
    ∑ i, b x i * fderiv ℝ f x (unitVector i)

/-- Draft of the well-posedness of the martingale problem (Stroock–Varadhan, Thm 7.2.1 with
Chapter 6; time-homogeneous case): for a symmetric continuous bounded uniformly elliptic
diffusion matrix and a bounded Borel drift, from every starting point there is exactly one
solution of the martingale problem for `½ Σ aᵢⱼ ∂ᵢ∂ⱼ + Σ bᵢ ∂ᵢ` on `C_c^∞`. -/
def svWellPosedStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (a : Vec d → Mat d) (b : Vec d → Vec d),
    Continuous a → (∀ x, (a x).transpose = a x) →
    (∃ M : ℝ, ∀ x i j, |a x i j| ≤ M) →
    (∃ c : ℝ, 0 < c ∧ ∀ x ξ, c * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ)) →
    Measurable b → (∃ M : ℝ, ∀ x i, |b x i| ≤ M) →
    ∀ x : Vec d, ∃! P : Measure (Path d), SolvesMartingaleProblem (svGenerator a b) x P

end EinsteinFull.External.Draft
