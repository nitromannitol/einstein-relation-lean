import EinsteinFull.Calculus.S4DivisionVector
import EinsteinFull.Frozen.CriticalVelocityTerm
import EinsteinRelation.TimeChange.EuclideanTransport

/-!
# The pure assembly of `e:division`

All data of the statement are abstracted: the first coefficient vector `aVec`, the eta coefficients,
the clock coordinates `χf` and the existence of expansions for every admissible `(λ, ℓ, η)`.
This file defines the reciprocal coefficients `recip`, the products `b`, the vector `c`, and bounds
the sum of their norms.
-/

open Finset
open EinsteinRelation EinsteinRelation.TimeChange

namespace EinsteinFull

/-- The eta coefficients extended by zero to all natural indices. -/
noncomputable def etaExt (d : ℕ) (etaC : Fin d → ℝ) : ℕ → ℝ := fun j =>
  if h : j < d then etaC ⟨j, h⟩ else 0

theorem etaExt_apply {d : ℕ} (etaC : Fin d → ℝ) (j : Fin d) : etaExt d etaC j.val = etaC j := by
  unfold etaExt
  rw [dif_pos j.isLt]

theorem abs_etaExt_le {d : ℕ} {C₁ : ℝ} (hC₁ : 0 ≤ C₁) {etaC : Fin d → ℝ}
    (h : ∀ j, |etaC j| ≤ C₁) (j : ℕ) : |etaExt d etaC j| ≤ C₁ := by
  unfold etaExt
  split_ifs with hj
  · exact h _
  · simpa using hC₁

/-- Coefficients of the reciprocal of the clock expansion. -/
noncomputable def divRecip (d : ℕ) (m : ℝ) (etaC : Fin d → ℝ) (n : Fin (d + 1)) : ℝ :=
  recipSeq m (etaExt d etaC) n.val

/-- Coefficients of the divided velocity expansion: the Cauchy product with the reciprocal. -/
noncomputable def divB (d : ℕ) (m : ℝ) (etaC : Fin d → ℝ) (aVec : Fin (d + 1) → Vec d)
    (n : Fin (d + 1)) : Vec d :=
  ∑ k : Fin (n.val + 1),
    divRecip d m etaC ⟨n.val - k.val, lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ •
      aVec ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt n.isLt)⟩

/-- The critical coefficient of the divided expansion. -/
noncomputable def divC {d : ℕ} (m : ℝ) (χf : Option (Fin d) → ℝ) (Ae : Vec d) : Vec d :=
  fun i => -2 / m * χf (some i) + 2 * χf none / m ^ 2 * Ae i

theorem euclideanNorm_sum_le {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Vec d) :
    euclideanNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, euclideanNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [euclideanNorm_eq_norm_toLp]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (euclideanNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem divRecip_zero (d : ℕ) (m : ℝ) (etaC : Fin d → ℝ) :
    divRecip d m etaC ⟨0, Nat.zero_lt_succ d⟩ = m⁻¹ := by
  unfold divRecip
  exact recipSeq_zero _ _

theorem divRecip_succ (d : ℕ) (m : ℝ) (etaC : Fin d → ℝ) (n : Fin (d + 1)) (hn : n.val ≠ 0) :
    divRecip d m etaC n = -m⁻¹ * ∑ j : Fin n.val, etaC ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.le_of_lt_succ n.isLt)⟩ *
      divRecip d m etaC ⟨n.val - (j.val + 1), lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ := by
  rcases n with ⟨_ | n', hlt⟩
  · exact absurd rfl hn
  · show recipSeq m (etaExt d etaC) (n' + 1) = _
    rw [recipSeq_succ]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => etaExt d etaC j * recipSeq m (etaExt d etaC) (n' - j)) (n' + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : etaExt d etaC j.val = etaC ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.le_of_lt_succ hlt)⟩ := etaExt_apply etaC ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.le_of_lt_succ hlt)⟩
    show etaExt d etaC j.val * recipSeq m (etaExt d etaC) (n' - j.val) = _
    rw [e1]
    show _ = _ * recipSeq m (etaExt d etaC) (n' + 1 - (j.val + 1))
    rw [Nat.add_sub_add_right]

theorem euclideanNorm_nonneg' {d : ℕ} (v : Vec d) : 0 ≤ euclideanNorm v :=
  Real.sqrt_nonneg _

theorem abs_divRecip_le {d : ℕ} {m C₁ Λ : ℝ} (hΛ : 0 ≤ Λ) (hC₁ : 0 ≤ C₁) (hmΛ : |m⁻¹| ≤ Λ)
    {etaC : Fin d → ℝ} (he : ∀ j, |etaC j| ≤ C₁) (n : Fin (d + 1)) :
    |divRecip d m etaC n| ≤ recipBound Λ C₁ d :=
  abs_recipSeq_le hmΛ hΛ hC₁ (abs_etaExt_le hC₁ he) d n.val (Nat.le_of_lt_succ n.isLt)

theorem euclideanNorm_divB_le {d : ℕ} {m C₁ Λ : ℝ} (hΛ : 0 ≤ Λ) (hC₁ : 0 ≤ C₁)
    (hmΛ : |m⁻¹| ≤ Λ) {etaC : Fin d → ℝ} (he : ∀ j, |etaC j| ≤ C₁)
    {aVec : Fin (d + 1) → Vec d} (haC : ∀ n, euclideanNorm (aVec n) ≤ C₁) (n : Fin (d + 1)) :
    euclideanNorm (divB d m etaC aVec n) ≤ ((d : ℝ) + 1) * (recipBound Λ C₁ d * C₁) := by
  have hB0 := recipBound_nonneg hΛ hC₁ d
  unfold divB
  refine (euclideanNorm_sum_le _ _).trans ?_
  calc ∑ k : Fin (n.val + 1), euclideanNorm (divRecip d m etaC
        ⟨n.val - k.val, lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ •
        aVec ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt n.isLt)⟩)
      ≤ ∑ _k : Fin (n.val + 1), recipBound Λ C₁ d * C₁ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [euclideanNorm_smul]
        exact mul_le_mul (abs_divRecip_le hΛ hC₁ hmΛ he _) (haC _) (euclideanNorm_nonneg' _) hB0
    _ = ((n.val : ℝ) + 1) * (recipBound Λ C₁ d * C₁) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((d : ℝ) + 1) * (recipBound Λ C₁ d * C₁) := by
        have : (n.val : ℝ) ≤ d := by exact_mod_cast Nat.le_of_lt_succ n.isLt
        exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hB0 hC₁)

theorem divC_eq {d : ℕ} (m : ℝ) (χf : Option (Fin d) → ℝ) (Ae : Vec d) :
    divC m χf Ae = (-2 / m) • (fun i => χf (some i)) + (2 * χf none / m ^ 2) • Ae := by
  funext i
  simp [divC]

theorem euclideanNorm_divC_le {d : ℕ} {m C₁ Λ : ℝ} (hΛ : 0 ≤ Λ) (hC₁ : 0 ≤ C₁)
    (hmΛ : |m⁻¹| ≤ Λ) {χf : Option (Fin d) → ℝ}
    (hχ : euclideanNorm (fun i => χf (some i)) + |χf none| ≤ C₁) {Ae : Vec d}
    (hAe : euclideanNorm Ae ≤ C₁) :
    euclideanNorm (divC m χf Ae) ≤ 2 * Λ * C₁ + 2 * C₁ * Λ ^ 2 * C₁ := by
  have h1 := euclideanNorm_nonneg' (fun i => χf (some i))
  have h2 : |χf none| ≤ C₁ := by linarith [abs_nonneg (χf none)]
  have h3 : euclideanNorm (fun i => χf (some i)) ≤ C₁ := by linarith [abs_nonneg (χf none)]
  rw [divC_eq]
  refine (euclideanNorm_add_le _ _).trans ?_
  rw [euclideanNorm_smul, euclideanNorm_smul]
  have e1 : |(-2 / m)| = 2 * |m⁻¹| := by
    rw [show (-2 / m : ℝ) = -2 * m⁻¹ by ring, abs_mul, abs_neg, abs_two]
  have e2 : |2 * χf none / m ^ 2| = 2 * |χf none| * (|m⁻¹| * |m⁻¹|) := by
    rw [show (2 * χf none / m ^ 2 : ℝ) = 2 * χf none * (m⁻¹ * m⁻¹) by ring, abs_mul, abs_mul,
      abs_mul, abs_two]
  have hm0 := abs_nonneg m⁻¹
  have t1 : |(-2 / m)| * euclideanNorm (fun i => χf (some i)) ≤ 2 * Λ * C₁ := by
    rw [e1]
    exact mul_le_mul (by linarith) h3 h1 (by positivity)
  have t2 : |2 * χf none / m ^ 2| * euclideanNorm Ae ≤ 2 * C₁ * Λ ^ 2 * C₁ := by
    rw [e2]
    have h4 : |m⁻¹| * |m⁻¹| ≤ Λ ^ 2 := by rw [sq]; exact mul_le_mul hmΛ hmΛ hm0 hΛ
    have h5 : 2 * |χf none| * (|m⁻¹| * |m⁻¹|) ≤ 2 * C₁ * Λ ^ 2 :=
      mul_le_mul (by linarith) h4 (mul_nonneg hm0 hm0) (by positivity)
    exact mul_le_mul h5 hAe (euclideanNorm_nonneg' _) (by positivity)
  linarith

end EinsteinFull
