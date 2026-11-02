import EinsteinRelation.External.AKMEnergyDensity

/-!
# Deterministic interior estimates used for Lemma 5.1

Proposed unfrozen contracts from Gilbarg--Trudinger, *Elliptic Partial
Differential Equations of Second Order*, 2001 reprint of the revised second
edition: Theorem 8.17, (8.46), p. 194, and Theorem 8.32, (8.86), p. 210.
Application: `paper/main.tex:727-729`.

These are explicitly the homogeneous divergence-form specializations needed
here: `b = c = d = f = g = 0`. In 8.17 this sets `ν = k(R) = 0`, and one may
choose any `q > n`; `p > 1` is retained. The measurable coefficient hypotheses
(8.5)--(8.6), including the entrywise square-sum bound, are retained.
The conclusion is almost everywhere, rather than a statement about arbitrary
representatives of Sobolev classes.

In 8.32 the domain is a ball and the interior domain is its concentric half
ball. Coefficients satisfy (8.5) and the full bounded Hölder condition (8.85).
The solution is already `C^{1,α}`, as required by the printed theorem. This
contract does not assert existence of such a representative from an H¹ class.
The conclusion records the gradient part of (8.86), with zero right-hand side.
All lengths, Hölder distances and gradient norms are Euclidean. Scalar Lᵖ
norms are unnormalized, as in the book. No deterministic result is asserted
as a Lean theorem in this file.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.External.GilbargTrudinger

open AKM

/-- The two principal-part inequalities (8.5)--(8.6). Symmetry is not required. -/
def EllipticBound {d : ℕ} (U : Set (Vec d)) (a : Vec d → Mat d) (lam Λ : ℝ) : Prop :=
  (∀ i j, Measurable (fun x => a x i j)) ∧
  ∀ x ∈ U, (∀ ξ, lam * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ)) ∧
    (∑ i, ∑ j, |a x i j| ^ 2) ≤ Λ ^ 2

/-- The actual Sobolev weak solution of the homogeneous equation. -/
def WeakSolution {d : ℕ} (U : Set (Vec d)) (a : Vec d → Mat d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  MemLp u 2 (volume.restrict U) ∧ MemLp g 2 (volume.restrict U) ∧
  HasWeakGradient U u g ∧
  HasWeakDivergence U (fun x => (a x).mulVec (g x)) (fun _ => 0)

/-- A full bounded `C^{0,α}` norm bound, expressed by upper bounds for the
supremum norm and Hölder seminorm whose sum is at most `K`. -/
def HolderBound {d : ℕ} (U : Set (Vec d)) (α : ℝ) (f : Vec d → ℝ) (K : ℝ) : Prop :=
  ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧ S + H ≤ K ∧
    (∀ x ∈ U, |f x| ≤ S) ∧
    ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ H * euclideanNorm (x - y) ^ α

/-- A `C^{1,α}` representative, including a bounded gradient and its Hölder
seminorm on `U`. The derivative is the actual Fréchet derivative. -/
def C1Alpha {d : ℕ} (U : Set (Vec d)) (α : ℝ)
    (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  (∀ x ∈ U, HasFDerivAt u
    (∑ i : Fin d, (g x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) x) ∧
  ∃ K : ℝ, ∀ i, HolderBound U α (fun x => g x i) K

/-- Ball specialization, with `p = 2` and `S = Ω`, of GT (7.45),
p. 164 (Lemmas 7.12 and 7.16). Both norms are unnormalized Euclidean
Lebesgue norms. The ball is convex; no boundary condition is imposed.
This proposed additional literature contract includes every radius and
center, and its constant depends only on the dimension.
Application: the Poincaré step in `paper/main.tex:722-729`. -/
def BallPoincareEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (y : Vec d) (R : ℝ), 0 < R →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        MemLp u 2 (volume.restrict (ball y R)) →
        MemLp g 2 (volume.restrict (ball y R)) → HasWeakGradient (ball y R) u g →
        Real.sqrt (∫ x in ball y R,
          |u x - ⨍ z in ball y R, u z ∂volume| ^ 2 ∂volume) ≤
          C * R * Real.sqrt (∫ x in ball y R, euclideanSq (g x) ∂volume)

/-- Homogeneous specialization of GT Theorem 8.17, (8.46), p. 194.
This contract permits dependence on `n, lam, Λ, p`; the printed estimate
has the stronger dependence on `n, Λ/lam, p` after setting `ν = k = 0`.
There is no sign condition (8.8), nor a symmetry assumption. -/
def LocalBoundednessEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (lam Λ p : ℝ), 0 < lam → 0 < Λ → 1 < p →
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Vec d)), IsOpen U →
      ∀ (a : Vec d → Mat d), EllipticBound U a lam Λ →
        ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), WeakSolution U a u g →
          ∀ (y : Vec d) (R : ℝ), 0 < R → ball y (2 * R) ⊆ U →
            MemLp u (ENNReal.ofReal p) (volume.restrict (ball y (2 * R))) →
            ∀ᵐ x ∂volume.restrict (ball y R),
              |u x| ≤ C * R ^ (-(d : ℝ) / p) *
                (∫ z in ball y (2 * R), |u z| ^ p ∂volume) ^ (1 / p)

/-- Gradient consequence of the homogeneous specialization of GT Theorem
8.32, (8.86), p. 210. On the ball of radius `2R`, the distance of the
interior ball to the boundary is `R`. The uniform coefficient norm in (8.85)
is bounded entry by entry by `K`; zero lower-order coefficients satisfy it.
The regular representative is a hypothesis, not the conclusion. -/
def InteriorGradientEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (lam K α R : ℝ),
    0 < lam → 0 < K → 0 < α → α < 1 → 0 < R →
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → Mat d),
      (∀ x ∈ ball 0 (2 * R), ∀ ξ, lam * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ)) →
      (∀ i j, HolderBound (ball 0 (2 * R)) α (fun x => a x i j) K) →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        WeakSolution (ball 0 (2 * R)) a u g →
        C1Alpha (ball 0 (2 * R)) α u g →
        ∀ M : ℝ, 0 ≤ M → (∀ x ∈ ball 0 (2 * R), |u x| ≤ M) →
          ∀ x ∈ ball 0 R, euclideanNorm (g x) ≤ C * M

/-- Proposed, unfrozen homogeneous interior consequence of Corollary 8.36,
(8.91), printed p. 212, with `T = ∅` and the principal-part hypotheses of
Theorem 8.32, p. 210. Application: `paper/main.tex:727-729`. The smaller
closed ball lies strictly inside the weak-solution domain, so local
`C¹,α` regularity gives a finite full gradient Hölder bound there.
Both representatives are identified in their Sobolev classes; no value
of the original weak gradient at a fixed point is asserted. This is a
literature proposition to be supplied as a hypothesis, not a proved input. -/
def InteriorRegularRepresentative : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (lam K α R : ℝ),
    0 < lam → 0 < K → 0 < α → α < 1 → 0 < R →
    ∀ (a : Vec d → Mat d),
      (∀ x ∈ ball 0 (2 * R), ∀ ξ,
        lam * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ)) →
      (∀ i j, HolderBound (ball 0 (2 * R)) α (fun x => a x i j) K) →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        WeakSolution (ball 0 (2 * R)) a u g →
        ∃ (v : Vec d → ℝ) (h : Vec d → Vec d),
          C1Alpha (ball 0 R) α v h ∧
          v =ᵐ[volume.restrict (ball 0 R)] u ∧
          h =ᵐ[volume.restrict (ball 0 R)] g

end EinsteinRelation.External.GilbargTrudinger
