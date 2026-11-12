import EinsteinRelation.Correctors.PoissonLift
import EinsteinRelation.Correctors.SpatialBallLocalL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! Source: `paper/main.tex:735-739`. The bounded normalized source
gives explicit coercivity and coefficient bounds for the Poisson lift. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Entry of `poissonLiftMatrix` at (0, 0). -/
lemma poissonLiftMatrix_zero_zero {d : ℕ} (F : Vec d) : poissonLiftMatrix F 0 0 = 1 + euclideanSq F := by
  simp [poissonLiftMatrix]

/-- Entry of `poissonLiftMatrix` at (0, k.succ). -/
lemma poissonLiftMatrix_zero_succ {d : ℕ} (F : Vec d) (k : Fin d) :
    poissonLiftMatrix F 0 k.succ = -F k := by
  simp [poissonLiftMatrix]

/-- Entry of `poissonLiftMatrix` at (k.succ, 0). -/
lemma poissonLiftMatrix_succ_zero {d : ℕ} (F : Vec d) (k : Fin d) :
    poissonLiftMatrix F k.succ 0 = -F k := by
  simp [poissonLiftMatrix]

/-- Entry of `poissonLiftMatrix` at (k.succ, l.succ). -/
lemma poissonLiftMatrix_succ_succ {d : ℕ} (F : Vec d) (k l : Fin d) :
    poissonLiftMatrix F k.succ l.succ = if k = l then 1 else 0 := by
  simp [poissonLiftMatrix]

/-- Explicit formula for the quadratic form of `poissonLiftMatrix`. -/
lemma poissonLiftMatrix_quadratic_form {d : ℕ} (F : Vec d) (ξ : Vec (d + 1)) :
    dot ξ ((poissonLiftMatrix F).mulVec ξ) =
    (1 + euclideanSq F) * (ξ 0) ^ 2 - 2 * (ξ 0) * (∑ k : Fin d, F k * ξ k.succ) +
    (∑ k : Fin d, (ξ k.succ) ^ 2) := by
  simp [dot, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ, poissonLiftMatrix_zero_zero, poissonLiftMatrix_zero_succ,
    poissonLiftMatrix_succ_zero, poissonLiftMatrix_succ_succ]
  have hsum1 : (∑ x : Fin d, ξ 0 * (F x * ξ x.succ)) = (ξ 0) * (∑ x : Fin d, F x * ξ x.succ) := by
    simp [Finset.mul_sum]
  have hsum2 : (∑ x : Fin d, ξ x.succ * (F x * ξ 0)) = (ξ 0) * (∑ x : Fin d, F x * ξ x.succ) := by
    calc
      (∑ x : Fin d, ξ x.succ * (F x * ξ 0)) = (∑ x : Fin d, ξ 0 * (F x * ξ x.succ)) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        ring
      _ = (ξ 0) * (∑ x : Fin d, F x * ξ x.succ) := by simp [Finset.mul_sum]
  have hsum3 : (∑ i : Fin d, 2 * ξ 0 * (F i * ξ i.succ)) = 2 * (ξ 0) * (∑ i : Fin d, F i * ξ i.succ) := by
    simp [Finset.mul_sum, mul_assoc]
  simp [Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum1, hsum2, hsum3]
  ring_nf

/-- The Frobenius norm squared of `poissonLiftMatrix` equals `(1 + |F|²)² + 2|F|² + d`. -/
lemma poissonLiftMatrix_frobenius_sq {d : ℕ} (F : Vec d) :
    (∑ i : Fin (d + 1), ∑ j : Fin (d + 1), (poissonLiftMatrix F i j) ^ 2) =
    (1 + euclideanSq F) ^ 2 + 2 * euclideanSq F + (d : ℝ) := by
  calc
    (∑ i : Fin (d + 1), ∑ j : Fin (d + 1), (poissonLiftMatrix F i j) ^ 2)
        = (∑ j : Fin (d + 1), (poissonLiftMatrix F 0 j) ^ 2) +
          (∑ k : Fin d, ∑ j : Fin (d + 1), (poissonLiftMatrix F k.succ j) ^ 2) := by
      rw [Fin.sum_univ_succ]
    _ = ((poissonLiftMatrix F 0 0) ^ 2 + ∑ k : Fin d, (poissonLiftMatrix F 0 k.succ) ^ 2) +
        (∑ k : Fin d, ((poissonLiftMatrix F k.succ 0) ^ 2 +
          ∑ l : Fin d, (poissonLiftMatrix F k.succ l.succ) ^ 2)) := by
      simp [Fin.sum_univ_succ]
    _ = ((1 + euclideanSq F) ^ 2 + ∑ k : Fin d, (-F k) ^ 2) +
        (∑ k : Fin d, ((-F k) ^ 2 + ∑ l : Fin d, (if k = l then 1 else 0) ^ 2)) := by
      simp [poissonLiftMatrix_zero_zero, poissonLiftMatrix_zero_succ,
        poissonLiftMatrix_succ_zero, poissonLiftMatrix_succ_succ]
    _ = ((1 + euclideanSq F) ^ 2 + ∑ k : Fin d, (F k) ^ 2) +
        (∑ k : Fin d, ((F k) ^ 2 + ∑ l : Fin d, (if k = l then 1 else 0) ^ 2)) := by
      simp
    _ = ((1 + euclideanSq F) ^ 2 + ∑ k : Fin d, (F k) ^ 2) +
        (∑ k : Fin d, (F k) ^ 2 + ∑ k : Fin d, ∑ l : Fin d, (if k = l then 1 else 0) ^ 2) := by
      simp [Finset.sum_add_distrib]
    _ = ((1 + euclideanSq F) ^ 2 + ∑ k : Fin d, (F k) ^ 2) +
        (∑ k : Fin d, (F k) ^ 2 + (d : ℝ)) := by
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    _ = (1 + euclideanSq F) ^ 2 + 2 * (∑ k : Fin d, (F k) ^ 2) + (d : ℝ) := by
      ring
    _ = (1 + euclideanSq F) ^ 2 + 2 * euclideanSq F + (d : ℝ) := by
      simp [euclideanSq, dot, pow_two]

/-- Unit bounded source vectors give dimension-uniform coercivity of the lift. -/
theorem poissonLiftMatrix_bounds {d : ℕ} (F : Vec d) (hF : euclideanNorm F ≤ 1) :
    (∀ ξ : Vec (d + 1), (1 / 4 : ℝ) * euclideanSq ξ ≤
      dot ξ ((poissonLiftMatrix F).mulVec ξ)) ∧
    (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      (poissonLiftMatrix F i j) ^ 2) ≤ (2 * ((d : ℝ) + 1)) ^ 2 := by
  have hFsq : euclideanSq F ≤ 1 := by
    have h_nonneg : 0 ≤ euclideanSq F := by
      rw [euclideanSq, dot]
      apply Finset.sum_nonneg
      intro i
      simpa [pow_two] using pow_two_nonneg (F i)
    have h_sqrt_sq := Real.sq_sqrt h_nonneg
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (euclideanSq F) := Real.sqrt_nonneg _
    have h_sq : (Real.sqrt (euclideanSq F)) * (Real.sqrt (euclideanSq F)) ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_self_le_mul_self h_sqrt_nonneg hF
    have h_sq' : (Real.sqrt (euclideanSq F)) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa [pow_two] using h_sq
    simpa [h_sqrt_sq] using h_sq'
  have hFsq_nonneg : 0 ≤ euclideanSq F := by
    rw [euclideanSq, dot]
    apply Finset.sum_nonneg
    intro i hi
    simpa [pow_two] using pow_two_nonneg (F i)
  have h_first : ∀ ξ : Vec (d + 1), (1 / 4 : ℝ) * euclideanSq ξ ≤
      dot ξ ((poissonLiftMatrix F).mulVec ξ) := by
    intro ξ
    rw [poissonLiftMatrix_quadratic_form F ξ, euclideanSq, dot]
    rw [Fin.sum_univ_succ]
    have h_cs : (∑ k : Fin d, F k * ξ k.succ) ^ 2 ≤
        (euclideanSq F) * (∑ k : Fin d, (ξ k.succ) ^ 2) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) F (fun k => ξ k.succ)
      simpa [dot, euclideanSq, pow_two] using this
    set s := euclideanSq F
    set A := ∑ k : Fin d, F k * ξ k.succ
    set S := ∑ k : Fin d, (ξ k.succ) ^ 2
    set x := ξ 0
    have hs_nonneg : 0 ≤ s := hFsq_nonneg
    have hS_nonneg : 0 ≤ S :=
      Finset.sum_nonneg (fun k _ => pow_two_nonneg (ξ k.succ))
    have h_cs' : A ^ 2 ≤ s * S := h_cs
    have h_main : 0 ≤ (3 + 4 * s) * x ^ 2 - 8 * x * A + 3 * S := by
      have h_sq_term : 0 ≤ ((3 + 4 * s) * x - 4 * A) ^ 2 := pow_two_nonneg _
      have h_discrim : 0 ≤ 3 * (3 + 4 * s) * S - 16 * A ^ 2 := by
        have h1 : 16 * A ^ 2 ≤ 16 * (s * S) := by nlinarith
        have h2 : 3 * (3 + 4 * s) * S - 16 * A ^ 2 ≥ 3 * (3 + 4 * s) * S - 16 * (s * S) := by nlinarith
        have h3 : 3 * (3 + 4 * s) * S - 16 * (s * S) = S * (9 - 4 * s) := by ring
        have h4 : 0 ≤ S * (9 - 4 * s) := by
          have h9s : 0 ≤ 9 - 4 * s := by nlinarith
          nlinarith
        nlinarith
      have h_eq : (3 + 4 * s) * ((3 + 4 * s) * x ^ 2 - 8 * x * A + 3 * S) =
          ((3 + 4 * s) * x - 4 * A) ^ 2 + (3 * (3 + 4 * s) * S - 16 * A ^ 2) := by
        ring
      have h_nonneg : 0 ≤ (3 + 4 * s) * ((3 + 4 * s) * x ^ 2 - 8 * x * A + 3 * S) := by
        rw [h_eq]
        nlinarith
      have h_pos : 0 < 3 + 4 * s := by nlinarith
      nlinarith
    have h_goal : (1 / 4 : ℝ) * (x ^ 2 + S) ≤ (1 + s) * x ^ 2 - 2 * x * A + S := by
      nlinarith
    simpa [S, pow_two] using h_goal
  have h_second : (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      (poissonLiftMatrix F i j) ^ 2) ≤ (2 * ((d : ℝ) + 1)) ^ 2 := by
    rw [poissonLiftMatrix_frobenius_sq F]
    set s := euclideanSq F
    have hs_nonneg : 0 ≤ s := hFsq_nonneg
    by_cases hd : d = 0
    · subst hd
      have hs0 : s = 0 := by
        simp [s, euclideanSq, dot]
      simp [hs0]
    · -- d ≥ 1
      have hd_one : (1 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast Nat.one_le_of_lt (Nat.pos_of_ne_zero hd)
      have h_bound : (1 + s) ^ 2 + 2 * s ≤ 6 := by
        nlinarith
      have h_total : 6 + (d : ℝ) ≤ (2 * ((d : ℝ) + 1)) ^ 2 := by
        nlinarith
      nlinarith
  exact And.intro h_first h_second

end EinsteinRelation.Correctors
