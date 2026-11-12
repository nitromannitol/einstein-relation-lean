import EinsteinRelation.Correctors.PoissonLiftCoefficient

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- A constant function has a Hölder bound with constant `|c|`. -/
private lemma holderBound_const {d : ℕ} {U : Set (Vec d)} {α : ℝ} (c : ℝ) :
    HolderBound U α (fun _ : Vec d => c) (|c|) := by
  refine ⟨|c|, 0, abs_nonneg _, by norm_num, by simp, ?_, ?_⟩
  · intro x _; rfl
  · intro x _ y _; simp

/-- Negation preserves the Hölder bound with the same constants. -/
private lemma holderBound_neg {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f : Vec d → ℝ} {K : ℝ}
    (hf : HolderBound U α f K) : HolderBound U α (-f) K := by
  obtain ⟨S, H, hS, hH, hK, hsup, hhold⟩ := hf
  refine ⟨S, H, hS, hH, hK, ?_, ?_⟩
  · intro x hx; simpa using hsup x hx
  · intro x hx y hy
    have h : (-f) x - (-f) y = -(f x - f y) := by
      simp [sub_eq_add_neg, add_comm]
    rw [h, abs_neg]
    exact hhold x hx y hy

/-- The square of a Hölder-bound function has a Hölder bound. -/
private lemma holderBound_sq {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f : Vec d → ℝ} {K : ℝ}
    (hf : HolderBound U α f K) : HolderBound U α (f ^ 2) (K ^ 2 + 2 * K * K) := by
  obtain ⟨S, H, hS, hH, hK, hsup, hhold⟩ := hf
  have hSK : S ≤ K := by nlinarith
  have hHK : H ≤ K := by nlinarith
  have h_bound : S ^ 2 + 2 * S * H ≤ K ^ 2 + 2 * K * K := by nlinarith
  have hS_sq_nonneg : 0 ≤ S ^ 2 := pow_two_nonneg _
  have h_two_SH_nonneg : 0 ≤ 2 * S * H := by nlinarith
  have h_euclidean_nonneg (x y : Vec d) : 0 ≤ euclideanNorm (x - y) :=
    Real.sqrt_nonneg _
  refine ⟨S ^ 2, 2 * S * H, hS_sq_nonneg, h_two_SH_nonneg, h_bound, ?_, ?_⟩
  · intro x hx
    have hfx : |f x| ≤ S := hsup x hx
    have hsq : |(f ^ 2) x| = |f x| ^ 2 := by simp [sq]
    rw [hsq]
    have hfx_abs_nonneg : 0 ≤ |f x| := abs_nonneg _
    nlinarith
  · intro x hx y hy
    have hdiff : (f ^ 2) x - (f ^ 2) y = (f x - f y) * (f x + f y) := by
      simp [sq]; ring
    rw [hdiff, abs_mul]
    have h1 : |f x - f y| ≤ H * euclideanNorm (x - y) ^ α := hhold x hx y hy
    have h2 : |f x + f y| ≤ 2 * S := by
      have h_abs_add : |f x + f y| ≤ |f x| + |f y| := abs_add_le _ _
      have hfx : |f x| ≤ S := hsup x hx
      have hfy : |f y| ≤ S := hsup y hy
      have hfx_abs_nonneg : 0 ≤ |f x| := abs_nonneg _
      have hfy_abs_nonneg : 0 ≤ |f y| := abs_nonneg _
      nlinarith
    have h_euclidean_pow_nonneg : 0 ≤ euclideanNorm (x - y) ^ α :=
      Real.rpow_nonneg (h_euclidean_nonneg x y) α
    have h_nonneg_fx_plus_fy : 0 ≤ |f x + f y| := abs_nonneg _
    have h_nonneg_H_euclidean : 0 ≤ H * euclideanNorm (x - y) ^ α := by
      nlinarith
    have hgoal := mul_le_mul h1 h2 h_nonneg_fx_plus_fy h_nonneg_H_euclidean
    -- hgoal: |f x - f y| * |f x + f y| ≤ (H * euclideanNorm (x - y) ^ α) * (2 * S)
    -- goal:   |f x - f y| * |f x + f y| ≤ (2 * S * H) * euclideanNorm (x - y) ^ α
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgoal

/-- Sum of two Hölder-bound functions has a Hölder bound with the sum of constants. -/
private lemma holderBound_add {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f g : Vec d → ℝ} {Kf Kg : ℝ}
    (hf : HolderBound U α f Kf) (hg : HolderBound U α g Kg) :
    HolderBound U α (f + g) (Kf + Kg) := by
  obtain ⟨Sf, Hf, hSf, hHf, hKf, hsupf, hholdf⟩ := hf
  obtain ⟨Sg, Hg, hSg, hHg, hKg, hsupg, hholdg⟩ := hg
  have hSfHg_nonneg : 0 ≤ Sf + Sg := by nlinarith
  have hHfHg_nonneg : 0 ≤ Hf + Hg := by nlinarith
  have hKfKg_bound : (Sf + Sg) + (Hf + Hg) ≤ Kf + Kg := by nlinarith
  have h_euclidean_nonneg (x y : Vec d) : 0 ≤ euclideanNorm (x - y) :=
    Real.sqrt_nonneg _
  refine ⟨Sf + Sg, Hf + Hg, hSfHg_nonneg, hHfHg_nonneg, hKfKg_bound, ?_, ?_⟩
  · intro x hx
    have hfx : |f x| ≤ Sf := hsupf x hx
    have hgx : |g x| ≤ Sg := hsupg x hx
    have h_abs_add : |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    have hfx_abs_nonneg : 0 ≤ |f x| := abs_nonneg _
    have hgx_abs_nonneg : 0 ≤ |g x| := abs_nonneg _
    calc
      |(f + g) x| = |f x + g x| := rfl
      _ ≤ |f x| + |g x| := h_abs_add
      _ ≤ Sf + Sg := by nlinarith
  · intro x hx y hy
    have hdiff : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
      simp; ring
    rw [hdiff]
    have h_abs_add : |(f x - f y) + (g x - g y)| ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
    have h1 : |f x - f y| ≤ Hf * euclideanNorm (x - y) ^ α := hholdf x hx y hy
    have h2 : |g x - g y| ≤ Hg * euclideanNorm (x - y) ^ α := hholdg x hx y hy
    have h_euclidean_pow_nonneg : 0 ≤ euclideanNorm (x - y) ^ α :=
      Real.rpow_nonneg (h_euclidean_nonneg x y) α
    calc
      |(f x - f y) + (g x - g y)| ≤ |f x - f y| + |g x - g y| := h_abs_add
      _ ≤ (Hf * euclideanNorm (x - y) ^ α) + (Hg * euclideanNorm (x - y) ^ α) := by nlinarith
      _ = (Hf + Hg) * euclideanNorm (x - y) ^ α := by ring

/-- Add a constant to a Hölder-bound function. -/
private lemma holderBound_add_const {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f : Vec d → ℝ} {K : ℝ}
    (hf : HolderBound U α f K) (c : ℝ) :
    HolderBound U α (fun x => f x + c) (K + |c|) := by
  have hc : HolderBound U α (fun _ : Vec d => c) (|c|) := holderBound_const c
  have h := holderBound_add hf hc
  simpa using h

/-- Sum over a Finset of Hölder-bound functions has a Hölder bound
    with constant equal to the sum of the individual constants. -/
private lemma holderBound_finset_sum {d : ℕ} {U : Set (Vec d)} {α : ℝ} {ι : Type*}
    [DecidableEq ι] (s : Finset ι) {f : ι → Vec d → ℝ} {K : ι → ℝ}
    (hf : ∀ i ∈ s, HolderBound U α (f i) (K i)) :
    HolderBound U α (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, K i) := by
  induction' s using Finset.induction_on with i s his IH
  · refine ⟨0, 0, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · intro x _; simp
    · intro x _ y _; simp
  · have h_rec := IH (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have h_i := hf i (Finset.mem_insert_self i s)
    have h_sum := holderBound_add h_rec h_i
    have h_sum_eq : (fun x => ∑ j ∈ insert i s, f j x) = (fun x => (∑ j ∈ s, f j x) + f i x) := by
      ext x; simp [Finset.sum_insert his, add_comm]
    rw [h_sum_eq]
    have h_const_eq : (∑ j ∈ insert i s, K j) = (∑ j ∈ s, K j) + K i := by
      simp [Finset.sum_insert his, add_comm]
    rw [h_const_eq]
    exact h_sum

/-- Sum of squares of the components of F has a Hölder bound.
    Each component `F x i` has bound `K`, so each `(F x i)^2` has bound `K^2 + 2*K*K`,
    and the sum of `d` such terms has bound `d * (K^2 + 2*K*K)`. -/
private lemma holderBound_sum_squares_components {d n : ℕ}
    (U : Set (Vec n)) (α K : ℝ) (F : Vec n → Vec d)
    (hF : ∀ i, HolderBound U α (fun x => F x i) K) :
    HolderBound U α (fun x : Vec n => ∑ i : Fin d, (F x i) ^ 2) ((d : ℝ) * (K ^ 2 + 2 * K * K)) := by
  have h_sq (i : Fin d) : HolderBound U α (fun x : Vec n => (F x i) ^ 2) (K ^ 2 + 2 * K * K) :=
    holderBound_sq (hF i)
  have h_all := holderBound_finset_sum (Finset.univ : Finset (Fin d))
    (fun i hi => h_sq i)
  -- The sum of constant (K^2 + 2*K*K) over Fin d is (d:ℝ) * (K^2 + 2*K*K)
  simpa [mul_add] using h_all

/-- If `HolderBound U α f C` and `C ≤ C'`, then `HolderBound U α f C'`. -/
private lemma holderBound_mono_const {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f : Vec d → ℝ} {C C' : ℝ}
    (hf : HolderBound U α f C) (hCC' : C ≤ C') :
    HolderBound U α f C' := by
  obtain ⟨S, H, hS, hH, hK, hsup, hhold⟩ := hf
  refine ⟨S, H, hS, hH, ?_, hsup, hhold⟩
  nlinarith

/-- Polynomial entries of the symmetric Poisson lift preserve bounded Hölder regularity.
Source: `paper/main.tex:735-739`. -/
theorem exists_holderBound_poissonLiftMatrix {d n : ℕ}
    (U : Set (Vec n)) (α K : ℝ) (F : Vec n → Vec d)
    (hF : ∀ i, HolderBound U α (fun x => F x i) K) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j,
      HolderBound U α (fun x => poissonLiftMatrix (F x) i j) C := by
  -- Build a bound for the (0,0) entry: 1 + sum of squares of components
  have h_sq_bound : HolderBound U α
      (fun x : Vec n => ∑ i : Fin d, (F x i) ^ 2) ((d : ℝ) * (K ^ 2 + 2 * K * K)) :=
    holderBound_sum_squares_components U α K F hF
  have h_zero_zero_bound : HolderBound U α
      (fun x : Vec n => poissonLiftMatrix (F x) 0 0) (|1| + (d : ℝ) * (K ^ 2 + 2 * K * K)) := by
    have h_entry : (fun x : Vec n => poissonLiftMatrix (F x) 0 0) =
        (fun x => (1 : ℝ) + (∑ i : Fin d, (F x i) ^ 2)) := by
      ext x
      simp [poissonLiftMatrix_zero_zero, euclideanSq, dot, pow_two]
    rw [h_entry]
    have h_sum := holderBound_add_const h_sq_bound (1 : ℝ)
    simpa [add_comm] using h_sum

  -- Choose C large enough to dominate all individual bounds
  let C := |1| + (d : ℝ) * (K ^ 2 + 2 * K * K) + |K| + 1
  have hC_pos : 0 < C := by
    have h1 : 0 < |(1 : ℝ)| := by norm_num
    have h_absK_nonneg : 0 ≤ |K| := abs_nonneg _
    have h_d_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    have hKsq_nonneg : 0 ≤ K ^ 2 := pow_two_nonneg _
    have h_inner_nonneg : 0 ≤ K ^ 2 + 2 * K * K := by nlinarith
    have h_nonneg : 0 ≤ (d : ℝ) * (K ^ 2 + 2 * K * K) + |K| + 1 := by nlinarith
    dsimp [C]
    nlinarith
  have hC_ge_sq : |1| + (d : ℝ) * (K ^ 2 + 2 * K * K) ≤ C := by
    dsimp [C]
    have h_absK_nonneg : 0 ≤ |K| := abs_nonneg _
    nlinarith
  have hC_ge_K : K ≤ C := by
    dsimp [C]
    have hK_le_abs : K ≤ |K| := le_abs_self K
    have h_absK_le_C : |K| ≤ |1| + (d : ℝ) * (K ^ 2 + 2 * K * K) + |K| + 1 := by
      have h_nonneg : 0 ≤ |1| + (d : ℝ) * (K ^ 2 + 2 * K * K) + 1 := by
        have h_one_nonneg : 0 ≤ |(1 : ℝ)| := abs_nonneg _
        have h_sq_nonneg : 0 ≤ K ^ 2 := pow_two_nonneg _
        have h_d_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        have h_inner_nonneg : 0 ≤ K ^ 2 + 2 * K * K := by nlinarith
        nlinarith
      nlinarith
    exact le_trans hK_le_abs h_absK_le_C
  have hC_ge_one : (1 : ℝ) ≤ C := by
    dsimp [C]
    have h_one_le_abs : (1 : ℝ) ≤ |(1 : ℝ)| := le_abs_self _
    nlinarith
  have hC_ge_zero : (0 : ℝ) ≤ C := by nlinarith

  have h_entry_bounds (i j : Fin (d + 1)) :
      HolderBound U α (fun x : Vec n => poissonLiftMatrix (F x) i j) C := by
    refine Fin.cases ?_ (fun k => ?_) i
    · -- i = 0
      refine Fin.cases ?_ (fun l => ?_) j
      · -- (0, 0)
        exact holderBound_mono_const h_zero_zero_bound hC_ge_sq
      · -- (0, l.succ) = -(F x l)
        have h_neg := holderBound_neg (hF l)
        exact holderBound_mono_const h_neg hC_ge_K
    · -- i = k.succ
      refine Fin.cases ?_ (fun l => ?_) j
      · -- (k.succ, 0) = -(F x k)
        have h_neg := holderBound_neg (hF k)
        exact holderBound_mono_const h_neg hC_ge_K
      · -- (k.succ, l.succ)
        by_cases hkl : k = l
        · subst hkl
          -- (k.succ, k.succ) = 1
          have h_one : HolderBound U α (fun _ : Vec n => (1 : ℝ)) (|(1 : ℝ)|) := holderBound_const 1
          have h_abs_one_le_C : |(1 : ℝ)| ≤ C := by
            have h_one_le_abs : (1 : ℝ) ≤ |(1 : ℝ)| := le_abs_self _
            nlinarith
          have h_eq : (fun x : Vec n => poissonLiftMatrix (F x) k.succ k.succ) =
              (fun _ : Vec n => (1 : ℝ)) := by
            ext x; simp [poissonLiftMatrix_succ_succ]
          rw [h_eq]
          exact holderBound_mono_const h_one h_abs_one_le_C
        · -- (k.succ, l.succ) = 0, k ≠ l
          have h_zero : HolderBound U α (fun _ : Vec n => (0 : ℝ)) (|(0 : ℝ)|) := holderBound_const 0
          have h_abs_zero_le_C : |(0 : ℝ)| ≤ C := by
            simp; exact hC_ge_zero
          have h_eq : (fun x : Vec n => poissonLiftMatrix (F x) k.succ l.succ) =
              (fun _ : Vec n => (0 : ℝ)) := by
            ext x; simp [poissonLiftMatrix_succ_succ, hkl]
          rw [h_eq]
          exact holderBound_mono_const h_zero h_abs_zero_le_C

  exact ⟨C, hC_pos, h_entry_bounds⟩
end EinsteinRelation.Correctors
