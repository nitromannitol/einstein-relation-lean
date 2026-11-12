import EinsteinRelationAudit.SharpExample.Vocabulary.External.AKMEnergyDensity

/-! Restated from the library module `EinsteinRelation.External.GilbargTrudinger`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

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
/-- Homogeneous specialization of GT Theorem 8.17, (8.46), p. 194.
This statement permits dependence on `n, lam, Λ, p`; the printed estimate
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
/-- Homogeneous interior consequence of Corollary 8.36,
(8.91), printed p. 212, with `T = ∅` and the principal-part hypotheses of
Theorem 8.32, p. 210. Application: `paper/main.tex:735-737`. The smaller
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
