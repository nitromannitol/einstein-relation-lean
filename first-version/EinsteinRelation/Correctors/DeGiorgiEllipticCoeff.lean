import Mathlib
import EinsteinRelation.External.GilbargTrudinger
import DeGiorgi.EllipticCoefficients
import EinsteinRelation.Correctors.MatrixInverseCoercivity
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-! # Elliptic coefficient fields on Euclidean balls

A measurable Gilbarg–Trudinger ellipticity bound on a set `U` restricts to a
`DeGiorgi.EllipticCoeff` on every Euclidean ball contained in `U`. The coefficient
is the coordinate pullback `x ↦ a (ofLp x)`, with lower constant `lam` and upper
constant `Λ ^ 2 / lam`. The coercivity of the inverse comes from
`coercive_inv_of_coercive_of_frobenius`.
-/

/-- The first standard basis vector has squared Euclidean norm one. -/
private theorem euclideanSq_single_zero {d : ℕ} [NeZero d] :
    euclideanSq (Pi.single (0 : Fin d) (1 : ℝ) : Vec d) = 1 := by
  unfold euclideanSq dot
  rw [Finset.sum_eq_single_of_mem (0 : Fin d) (Finset.mem_univ _)]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, hi]

/-- The quadratic form of `M` at the first basis vector is the entry `M 0 0`. -/
private theorem dot_single_mulVec_zero {d : ℕ} [NeZero d] (M : Mat d) :
    dot (Pi.single (0 : Fin d) (1 : ℝ) : Vec d)
      (M.mulVec (Pi.single (0 : Fin d) (1 : ℝ) : Vec d)) = M 0 0 := by
  have hcol : ∀ i : Fin d, M.mulVec (Pi.single (0 : Fin d) (1 : ℝ) : Vec d) i = M i 0 := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single_of_mem (0 : Fin d) (Finset.mem_univ _)]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
  unfold dot
  rw [Finset.sum_eq_single_of_mem (0 : Fin d) (Finset.mem_univ _)]
  · simp [hcol]
  · intro i _ hi
    simp [Pi.single_apply, hi]

/-- A coercive bound at one point forces `lam ≤ Λ ^ 2 / lam`. -/
private theorem le_sq_div_of_bound {d : ℕ} [NeZero d] {M : Mat d} {lam Λ : ℝ}
    (hlam : 0 < lam)
    (hcoer : ∀ ξ : Vec d, lam * euclideanSq ξ ≤ dot ξ (M.mulVec ξ))
    (hfrob : (∑ i, ∑ j, |M i j| ^ 2) ≤ Λ ^ 2) : lam ≤ Λ ^ 2 / lam := by
  have h1 : lam ≤ M 0 0 := by
    have h := hcoer (Pi.single (0 : Fin d) (1 : ℝ) : Vec d)
    rw [euclideanSq_single_zero, dot_single_mulVec_zero, mul_one] at h
    exact h
  have hrow : |M 0 0| ^ 2 ≤ ∑ j, |M 0 j| ^ 2 :=
    Finset.single_le_sum (f := fun j => |M 0 j| ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ 0)
  have hall : ∑ j, |M 0 j| ^ 2 ≤ ∑ i, ∑ j, |M i j| ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j, |M i j| ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ 0)
  have h2 : |M 0 0| ^ 2 ≤ Λ ^ 2 := (hrow.trans hall).trans hfrob
  rw [sq_abs] at h2
  rw [le_div_iff₀ hlam]
  calc lam * lam ≤ M 0 0 * M 0 0 := mul_self_le_mul_self hlam.le h1
    _ = M 0 0 ^ 2 := (sq _).symm
    _ ≤ Λ ^ 2 := h2

/-- The squared Euclidean norm of a vector of `EuclideanSpace` is its coordinate
sum of squares. -/
private theorem norm_sq_eq_euclideanSq {d : ℕ} (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖ξ‖ ^ 2 = euclideanSq (WithLp.ofLp ξ) := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold euclideanSq dot
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, sq]

/-- The Euclidean pairing `⟪ξ, M ξ⟫` written in coordinates. -/
private theorem inner_matMulE_eq {d : ℕ} (M : Mat d) (ξ : EuclideanSpace ℝ (Fin d)) :
    inner ℝ ξ (DeGiorgi.matMulE M ξ) = dot (WithLp.ofLp ξ) (M.mulVec (WithLp.ofLp ξ)) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', RCLike.conj_to_real,
    DeGiorgi.matMulE_apply, dot]

/-- A point of the Euclidean ball in `EuclideanSpace` lies in the Euclidean ball
`External.AKM.ball` after taking coordinates. -/
private theorem ofLp_mem_akm_ball {d : ℕ} {y : Vec d} {R : ℝ}
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R) :
    WithLp.ofLp x ∈ External.AKM.ball y R := by
  have hsum : ∑ i, dist (x i) ((WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) i) ^ 2 =
      euclideanSq (WithLp.ofLp x - y) := by
    unfold euclideanSq dot
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.dist_eq, sq_abs]
    change (WithLp.ofLp x i - y i) ^ 2 = (WithLp.ofLp x i - y i) * (WithLp.ofLp x i - y i)
    ring
  rw [Metric.mem_ball, EuclideanSpace.dist_eq, hsum] at hx
  show euclideanNorm (WithLp.ofLp x - y) < R
  unfold euclideanNorm
  exact hx

/-- A Gilbarg–Trudinger ellipticity bound on `U` restricts to a `DeGiorgi.EllipticCoeff`
on every nonempty Euclidean ball contained in `U`. -/
theorem exists_ellipticCoeff_of_ellipticBound {d : ℕ} [NeZero d] {U : Set (Vec d)}
    {a : Vec d → Mat d} {lam Λ : ℝ} (hlam : 0 < lam)
    (ha : External.GilbargTrudinger.EllipticBound U a lam Λ)
    {y : Vec d} {R : ℝ} (hB : External.AKM.ball y R ⊆ U)
    (hBne : (External.AKM.ball y R).Nonempty) :
    ∃ A : DeGiorgi.EllipticCoeff d
        (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R),
      A.a = (fun x => a (WithLp.ofLp x)) ∧ A.lam = lam ∧ A.Λ = Λ ^ 2 / lam := by
  obtain ⟨hmeas, hpt⟩ := ha
  have hmeasEu : Measurable (fun x : EuclideanSpace ℝ (Fin d) => WithLp.ofLp x) :=
    WithLp.measurable_ofLp 2 (Fin d → ℝ)
  have hpoint : ∀ x ∈ Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R,
      (∀ ξ : Vec d, lam * euclideanSq ξ ≤ dot ξ ((a (WithLp.ofLp x)).mulVec ξ)) ∧
        (∑ i, ∑ j, |a (WithLp.ofLp x) i j| ^ 2) ≤ Λ ^ 2 :=
    fun x hx => hpt _ (hB (ofLp_mem_akm_ball hx))
  have hΛ : lam ≤ Λ ^ 2 / lam := by
    obtain ⟨z, hz⟩ := hBne
    obtain ⟨hcoer, hfrob⟩ := hpt z (hB hz)
    exact le_sq_div_of_bound hlam hcoer hfrob
  refine ⟨{ a := fun x => a (WithLp.ofLp x), lam := lam, Λ := Λ ^ 2 / lam,
            measurable_comp := fun i j => (hmeas i j).comp hmeasEu,
            hlam := hlam, hΛ := hΛ, coercive := ?_, coercive_inv := ?_ }, rfl, rfl, rfl⟩
  · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
    obtain ⟨hcoer, _⟩ := hpoint x hx
    intro ξ
    rw [norm_sq_eq_euclideanSq, inner_matMulE_eq]
    exact hcoer (WithLp.ofLp ξ)
  · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
    obtain ⟨hcoer, hfrob⟩ := hpoint x hx
    intro ξ
    rw [inv_div, norm_sq_eq_euclideanSq, inner_matMulE_eq]
    exact (coercive_inv_of_coercive_of_frobenius hlam hcoer hfrob).2 (WithLp.ofLp ξ)

end EinsteinRelation.Correctors
