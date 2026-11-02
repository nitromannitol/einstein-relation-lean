import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Weighted annulus sums

Real-analysis support for `p:tail#annuli`: if the annulus norms `a k` are bounded by
`K * min (s ^ h) (s ^ (-N) * exp (-c k ^ 2))`, then the exponentially weighted sums obey
the bounds of the statement, with constants independent of `s ∈ (0, exp (-1)]`.
-/

namespace EinsteinFull.AnnuliSupport

theorem one_le_log_inv {s : ℝ} (hs : 0 < s) (hs1 : s ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / s) := by
  rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hs]
  calc Real.exp 1 * s ≤ Real.exp 1 * Real.exp (-1) := by gcongr
    _ = 1 := by rw [← Real.exp_add]; simp

theorem rpow_eq_exp_log_inv {s : ℝ} (hs : 0 < s) (x : ℝ) :
    s ^ x = Real.exp (-(Real.log (1 / s)) * x) := by
  rw [Real.rpow_def_of_pos hs, one_div, Real.log_inv]
  congr 1
  ring

theorem exp_weight_le (c w : ℝ) (hc : 0 < c) (k : ℕ) :
    Real.exp (w * ((k + 1 : ℕ) : ℝ) - c / 2 * (k : ℝ) ^ 2) ≤
      Real.exp (w + (w + 1) ^ 2 / (2 * c)) * Real.exp (-(k : ℝ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h : (w + 1) * (k : ℝ) - c / 2 * (k : ℝ) ^ 2 ≤ (w + 1) ^ 2 / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (c * (k : ℝ) - (w + 1))]
  push_cast
  nlinarith [h]

theorem annuli_sum_bounds (c : ℝ) (hc : 0 < c) (N : ℕ) (h : ℝ) (hh : 0 < h) (w : ℝ)
    (hw : 0 ≤ w) (K : ℝ) (hK : 0 < K) :
    ∃ C C₂ : ℝ, 0 < C ∧ 0 < C₂ ∧ ∀ s : ℝ, 0 < s → s ≤ Real.exp (-1) → ∀ a : ℕ → ℝ,
      (∀ k, 0 ≤ a k) →
      (∀ k : ℕ, a k ≤ K * min (s ^ h) (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2))) →
      Summable (fun k : ℕ => Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k) ∧
      (∑' k : ℕ, Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k) ≤
        C * s ^ h * Real.exp (C * Real.sqrt (Real.log (1 / s))) ∧
      (∑' k : ℕ, if ⌈1 + C₂ * Real.sqrt (Real.log (1 / s))⌉₊ < k + 1 then
        Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k else 0) ≤ C * s ^ (h + 1) := by
  obtain ⟨eM, heM⟩ : ∃ eM : ℝ, eM = Real.exp (w + (w + 1) ^ 2 / (2 * c)) := ⟨_, rfl⟩
  have heM0 : 0 < eM := by rw [heM]; exact Real.exp_pos _
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑' k : ℕ, Real.exp (-(k : ℝ)) := ⟨_, rfl⟩
  have hGs : Summable (fun k : ℕ => Real.exp (-(k : ℝ))) := Real.summable_exp_neg_nat
  have hG0 : 0 ≤ G := by rw [hG]; exact tsum_nonneg fun k => (Real.exp_pos _).le
  have hNh : 0 < (N : ℝ) + h + 1 := by positivity
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = Real.sqrt (2 * ((N : ℝ) + h + 1) / c) := ⟨_, rfl⟩
  have hC₂pos : 0 < C₂ := by rw [hC₂]; exact Real.sqrt_pos.2 (by positivity)
  have hcC₂ : c * C₂ ^ 2 = 2 * ((N : ℝ) + h + 1) := by
    rw [hC₂, Real.sq_sqrt (by positivity)]
    field_simp
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (1 + w) * (2 + C₂) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; exact mul_nonneg (by linarith) (by linarith)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max (K * (1 + eM * G)) D := ⟨_, rfl⟩
  have hCK : K * (1 + eM * G) ≤ C := by rw [hC]; exact le_max_left _ _
  have hCD : D ≤ C := by rw [hC]; exact le_max_right _ _
  have hCpos : 0 < C :=
    lt_of_lt_of_le (mul_pos hK (by linarith [mul_nonneg heM0.le hG0])) hCK
  refine ⟨C, C₂, hCpos, hC₂pos, ?_⟩
  intro s hs hs1 a ha hab
  have hL1 := one_le_log_inv hs hs1
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (1 / s) := ⟨_, rfl⟩
  rw [← hL] at hL1 ⊢
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt L := ⟨_, rfl⟩
  rw [← hq]
  have hq1 : 1 ≤ q := by
    rw [hq]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hL1
  have hqsq : q ^ 2 = L := by rw [hq]; exact Real.sq_sqrt (by linarith)
  have hC₂q : 0 ≤ C₂ * q := mul_nonneg hC₂pos.le (by linarith)
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, n0 = ⌈1 + C₂ * q⌉₊ := ⟨_, rfl⟩
  rw [← hn0]
  have hn0le : (n0 : ℝ) ≤ (2 + C₂) * q := by
    have h1 : (n0 : ℝ) < 1 + C₂ * q + 1 := by
      rw [hn0]; exact Nat.ceil_lt_add_one (by linarith)
    nlinarith
  have hs1' : s ≤ 1 := hs1.trans (Real.exp_le_one_iff.2 (by norm_num))
  have hsh : 0 < s ^ h := Real.rpow_pos_of_pos hs h
  have hsh1 : 0 < s ^ (h + 1) := Real.rpow_pos_of_pos hs _
  have hA : 0 ≤ s ^ (-(N : ℝ)) := (Real.rpow_pos_of_pos hs _).le
  -- the tail terms
  have htail : ∀ k : ℕ, n0 < k + 1 → Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k ≤
      K * s ^ (h + 1) * (eM * Real.exp (-(k : ℝ))) := by
    intro k hk
    have hkq : C₂ * q < k := by
      have h1 : 1 + C₂ * q ≤ (n0 : ℝ) := by rw [hn0]; exact Nat.le_ceil _
      have h2 : (n0 : ℝ) < (k : ℝ) + 1 := by exact_mod_cast hk
      linarith
    have hk2 : C₂ ^ 2 * L < (k : ℝ) ^ 2 := by
      have h3 : (C₂ * q) ^ 2 < (k : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hC₂q (sub_pos.2 hkq).le, mul_pos (sub_pos.2 hkq) (sub_pos.2 hkq)]
      calc C₂ ^ 2 * L = (C₂ * q) ^ 2 := by rw [mul_pow, hqsq]
        _ < _ := h3
    have hk3 : ((N : ℝ) + h + 1) * L ≤ c / 2 * (k : ℝ) ^ 2 := by
      have e : c * (C₂ ^ 2 * L) = 2 * ((N : ℝ) + h + 1) * L := by
        rw [← mul_assoc, hcC₂]
      linarith [mul_lt_mul_of_pos_left hk2 hc, e]
    have hZ1 : Real.exp (-(c / 2) * (k : ℝ) ^ 2) ≤ s ^ ((N : ℝ) + h + 1) := by
      rw [rpow_eq_exp_log_inv hs, ← hL]
      apply Real.exp_le_exp.2
      nlinarith [hk3]
    have hZ2 : Real.exp (w * ((k + 1 : ℕ) : ℝ) - c / 2 * (k : ℝ) ^ 2) ≤
        eM * Real.exp (-(k : ℝ)) := by
      rw [heM]; exact exp_weight_le c w hc k
    have hAB : s ^ (-(N : ℝ)) * s ^ ((N : ℝ) + h + 1) = s ^ (h + 1) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    have hexp : Real.exp (w * ((k + 1 : ℕ) : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2) =
        Real.exp (-(c / 2) * (k : ℝ) ^ 2) *
          Real.exp (w * ((k + 1 : ℕ) : ℝ) - c / 2 * (k : ℝ) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have step1 : a k ≤ K * (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2)) :=
      (hab k).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le)
    calc Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k
        ≤ Real.exp (w * ((k + 1 : ℕ) : ℝ)) *
            (K * (s ^ (-(N : ℝ)) * Real.exp (-c * (k : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left step1 (Real.exp_pos _).le
      _ = K * s ^ (-(N : ℝ)) * (Real.exp (-(c / 2) * (k : ℝ) ^ 2) *
            Real.exp (w * ((k + 1 : ℕ) : ℝ) - c / 2 * (k : ℝ) ^ 2)) := by
          rw [← hexp]; ring
      _ ≤ K * s ^ (-(N : ℝ)) * (s ^ ((N : ℝ) + h + 1) * (eM * Real.exp (-(k : ℝ)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hZ1 hZ2 (Real.exp_pos _).le (Real.rpow_pos_of_pos hs _).le)
            (mul_nonneg hK.le hA)
      _ = K * s ^ (h + 1) * (eM * Real.exp (-(k : ℝ))) := by rw [← hAB]; ring
  -- split into head and tail
  obtain ⟨tl, htl⟩ : ∃ tl : ℕ → ℝ, tl = fun k : ℕ =>
      if n0 < k + 1 then Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k else 0 := ⟨_, rfl⟩
  obtain ⟨hd, hhd⟩ : ∃ hd : ℕ → ℝ, hd = fun k : ℕ =>
      if n0 < k + 1 then 0 else Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k := ⟨_, rfl⟩
  have hsplit : ∀ k : ℕ, Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k = hd k + tl k := by
    intro k
    by_cases hk : n0 < k + 1
    · rw [htl, hhd]; simp only [hk, ↓reduceIte, zero_add]
    · rw [htl, hhd]; simp only [hk, ↓reduceIte, add_zero]
  have hgs : Summable (fun k : ℕ => K * s ^ (h + 1) * (eM * Real.exp (-(k : ℝ)))) :=
    (hGs.mul_left eM).mul_left _
  have htl_le : ∀ k, tl k ≤ K * s ^ (h + 1) * (eM * Real.exp (-(k : ℝ))) := by
    intro k
    by_cases hk : n0 < k + 1
    · simp only [htl, if_pos hk]; exact htail k hk
    · simp only [htl, if_neg hk]
      exact mul_nonneg (mul_nonneg hK.le hsh1.le) (mul_nonneg heM0.le (Real.exp_pos _).le)
  have htl_nn : ∀ k, 0 ≤ tl k := by
    intro k
    by_cases hk : n0 < k + 1
    · simp only [htl, if_pos hk]; exact mul_nonneg (Real.exp_pos _).le (ha k)
    · simp only [htl, if_neg hk]; exact le_rfl
  have htl_s : Summable tl := Summable.of_nonneg_of_le htl_nn htl_le hgs
  have htl_tsum : ∑' k, tl k ≤ K * s ^ (h + 1) * (eM * G) := by
    calc ∑' k, tl k ≤ ∑' k : ℕ, K * s ^ (h + 1) * (eM * Real.exp (-(k : ℝ))) :=
          htl_s.tsum_le_tsum htl_le hgs
      _ = K * s ^ (h + 1) * (eM * G) := by rw [tsum_mul_left, tsum_mul_left, hG]
  have hhd_zero : ∀ k ∉ Finset.range n0, hd k = 0 := by
    intro k hk
    have h1 : n0 ≤ k := by simpa using hk
    have h2 : n0 < k + 1 := Nat.lt_succ_of_le h1
    simp only [hhd, h2, ↓reduceIte]
  have hhd_s : Summable hd := summable_of_ne_finset_zero hhd_zero
  have hhd_le : ∀ k, hd k ≤ Real.exp (w * (n0 : ℝ)) * (K * s ^ h) := by
    intro k
    by_cases hk : n0 < k + 1
    · simp only [hhd, if_pos hk]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hK.le hsh.le)
    · simp only [hhd, if_neg hk]
      have hk' : k + 1 ≤ n0 := not_lt.1 hk
      have h1 : Real.exp (w * ((k + 1 : ℕ) : ℝ)) ≤ Real.exp (w * (n0 : ℝ)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hk') hw)
      have h2 : a k ≤ K * s ^ h :=
        (hab k).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK.le)
      exact mul_le_mul h1 h2 (ha k) (Real.exp_pos _).le
  have hhd_tsum : ∑' k, hd k ≤ (n0 : ℝ) * (Real.exp (w * (n0 : ℝ)) * (K * s ^ h)) := by
    rw [tsum_eq_sum hhd_zero]
    calc ∑ k ∈ Finset.range n0, hd k
        ≤ ∑ k ∈ Finset.range n0, Real.exp (w * (n0 : ℝ)) * (K * s ^ h) :=
          Finset.sum_le_sum fun k _ => hhd_le k
      _ = (n0 : ℝ) * (Real.exp (w * (n0 : ℝ)) * (K * s ^ h)) := by simp
  have hsum_s : Summable (fun k : ℕ => Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k) :=
    (hhd_s.add htl_s).congr fun k => (hsplit k).symm
  have hsum_eq : ∑' k : ℕ, Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k =
      ∑' k, hd k + ∑' k, tl k := by
    rw [← hhd_s.tsum_add htl_s]
    exact tsum_congr hsplit
  have hE1 : 1 ≤ Real.exp (D * q) := Real.one_le_exp (mul_nonneg hD0 (by linarith))
  have hE2 : Real.exp (D * q) ≤ Real.exp (C * q) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hCD (by linarith))
  have hn0exp : (n0 : ℝ) * Real.exp (w * (n0 : ℝ)) ≤ Real.exp (D * q) := by
    have h1 : (n0 : ℝ) ≤ Real.exp (n0 : ℝ) := by linarith [Real.add_one_le_exp (n0 : ℝ)]
    calc (n0 : ℝ) * Real.exp (w * (n0 : ℝ)) ≤ Real.exp (n0 : ℝ) * Real.exp (w * (n0 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp ((1 + w) * (n0 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (D * q) := by
          apply Real.exp_le_exp.2
          rw [hD, mul_assoc]
          exact mul_le_mul_of_nonneg_left hn0le (by linarith)
  have hs_le : s ^ (h + 1) ≤ s ^ h :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1' (by linarith)
  refine ⟨hsum_s, ?_, ?_⟩
  · rw [hsum_eq]
    have hu : 0 ≤ K * s ^ h := mul_nonneg hK.le hsh.le
    have hv : 0 ≤ eM * G := mul_nonneg heM0.le hG0
    calc ∑' k, hd k + ∑' k, tl k
        ≤ (n0 : ℝ) * (Real.exp (w * (n0 : ℝ)) * (K * s ^ h)) +
            K * s ^ (h + 1) * (eM * G) := add_le_add hhd_tsum htl_tsum
      _ ≤ Real.exp (D * q) * (K * s ^ h) + (K * s ^ h) * (eM * G) := by
          apply add_le_add
          · calc (n0 : ℝ) * (Real.exp (w * (n0 : ℝ)) * (K * s ^ h))
                = ((n0 : ℝ) * Real.exp (w * (n0 : ℝ))) * (K * s ^ h) := by ring
              _ ≤ Real.exp (D * q) * (K * s ^ h) :=
                mul_le_mul_of_nonneg_right hn0exp hu
          · calc K * s ^ (h + 1) * (eM * G) = K * (s ^ (h + 1) * (eM * G)) := by ring
              _ ≤ K * (s ^ h * (eM * G)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs_le hv) hK.le
              _ = (K * s ^ h) * (eM * G) := by ring
      _ ≤ Real.exp (D * q) * ((K * s ^ h) * (1 + eM * G)) := by
          nlinarith [mul_nonneg (mul_nonneg hu hv) (sub_nonneg.2 hE1)]
      _ ≤ Real.exp (C * q) * (C * s ^ h) := by
          have h3 : (K * s ^ h) * (1 + eM * G) ≤ C * s ^ h := by
            calc (K * s ^ h) * (1 + eM * G) = s ^ h * (K * (1 + eM * G)) := by ring
              _ ≤ s ^ h * C := mul_le_mul_of_nonneg_left hCK hsh.le
              _ = C * s ^ h := mul_comm _ _
          exact mul_le_mul hE2 h3 (mul_nonneg hu (by linarith)) (Real.exp_pos _).le
      _ = C * s ^ h * Real.exp (C * q) := by ring
  · rw [show (∑' k : ℕ, if n0 < k + 1 then Real.exp (w * ((k + 1 : ℕ) : ℝ)) * a k else 0) =
        ∑' k, tl k by rw [htl]]
    calc ∑' k, tl k ≤ K * s ^ (h + 1) * (eM * G) := htl_tsum
      _ = s ^ (h + 1) * (K * (eM * G)) := by ring
      _ ≤ s ^ (h + 1) * C :=
          mul_le_mul_of_nonneg_left (by linarith only [hK, hCK]) hsh1.le
      _ = C * s ^ (h + 1) := mul_comm _ _

end EinsteinFull.AnnuliSupport
