import EinsteinRelation.Sharpness.CoordinateIterates
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Uniform derivative bounds for families of smooth functions on `Vec d`.

`UnifBdd F` says that every `F a` is smooth and every Fréchet derivative of every `F a` is bounded
in operator norm, with a bound that depends on the order only. The class is closed under the
algebraic operations and under composition with a smooth function on a compact interval; it is
interchangeable with uniform bounds on all iterated coordinate derivatives. It is used for the
physical coefficient and potential of the sharpness example (`paper/main.tex:1534–1541`). -/

open Set
open scoped Nat

namespace EinsteinFull.Calculus.S1

open EinsteinRelation EinsteinRelation.Sharpness

theorem contDiff_nat_of_top {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : ℕ) : ContDiff ℝ k f :=
  hf.of_le (by exact_mod_cast le_top)

theorem norm_unitVector_le_one {d : ℕ} (i : Fin d) : ‖unitVector i‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h
    simp [unitVector]
  · simp [unitVector, Pi.single_apply, h]

theorem abs_apply_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

theorem norm_le_euclideanNorm {d : ℕ} (v : Vec d) : ‖v‖ ≤ euclideanNorm v := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_apply_le_euclideanNorm v i

theorem multilinear_expand {d k : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vec d) ℝ)
    (v : Fin k → Vec d) :
    T v = ∑ dirs : Fin k → Fin d, (∏ j, v j (dirs j)) * T (fun j => unitVector (dirs j)) := by
  classical
  have hv (j : Fin k) : (∑ i : Fin d, v j i • unitVector i) = v j := by
    ext i
    simp [unitVector, Pi.single_apply]
  calc
    T v = T (fun j => ∑ i : Fin d, v j i • unitVector i) := by
      simp only [hv]
    _ = ∑ dirs : Fin k → Fin d, T (fun j => v j (dirs j) • unitVector (dirs j)) :=
      T.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro dirs _
      rw [T.map_smul_univ, smul_eq_mul]

theorem iteratedFDeriv_basis {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
    iteratedFDeriv ℝ k f x (fun j => unitVector (dirs j)) =
      iteratedCoordinateDerivative (List.ofFn dirs) f x := by
  induction k generalizing x with
  | zero => simp only [List.ofFn_zero, iteratedFDeriv_zero_apply,
      iteratedCoordinateDerivative_nil]
  | succ k ih =>
    rw [List.ofFn_succ, iteratedCoordinateDerivative_cons, iteratedFDeriv_succ_apply_left]
    change (fderiv ℝ (iteratedFDeriv ℝ k f) x) (unitVector (dirs 0))
        (fun j => unitVector (dirs j.succ)) =
      (fderiv ℝ (iteratedCoordinateDerivative (List.ofFn (fun j => dirs j.succ)) f) x)
        (unitVector (dirs 0))
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      hf.differentiable_iteratedFDeriv (mod_cast ENat.coe_lt_top k) x
    rw [← fderiv_continuousMultilinear_apply_const_apply hdiff]
    have heq : (fun y => iteratedFDeriv ℝ k f y (fun j => unitVector (dirs j.succ))) =
        iteratedCoordinateDerivative (List.ofFn (fun j => dirs j.succ)) f :=
      funext (ih (fun j => dirs j.succ))
    rw [heq]

/-- Every `F a` is smooth and its Fréchet derivatives are bounded uniformly in `a` and `x`. -/
def UnifBdd {ι : Type*} {d : ℕ} (F : ι → Vec d → ℝ) : Prop :=
  (∀ a, ContDiff ℝ (⊤ : ℕ∞) (F a)) ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (F a) x‖ ≤ C

section Algebra

variable {ι : Type*} {d : ℕ}

theorem UnifBdd.congr {F G : ι → Vec d → ℝ} (hF : UnifBdd F) (h : ∀ a x, F a x = G a x) :
    UnifBdd G := by
  have : F = G := funext fun a => funext (h a)
  exact this ▸ hF

theorem unifBdd_const (c : ℝ) : UnifBdd (fun (_ : ι) (_ : Vec d) => c) := by
  refine ⟨fun _ => contDiff_const, fun k => ⟨‖c‖, fun a x => ?_⟩⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fun _ : Vec d => c) (x := x)).le
  · have h0 : iteratedFDeriv ℝ k (fun _ : Vec d => c) = 0 := iteratedFDeriv_const_of_ne hk.ne' c
    show ‖iteratedFDeriv ℝ k (fun _ : Vec d => c) x‖ ≤ ‖c‖
    rw [h0]
    simp

theorem UnifBdd.add {F G : ι → Vec d → ℝ} (hF : UnifBdd F) (hG : UnifBdd G) :
    UnifBdd (fun a x => F a x + G a x) := by
  refine ⟨fun a => (hF.1 a).add (hG.1 a), fun k => ?_⟩
  obtain ⟨C, hC⟩ := hF.2 k
  obtain ⟨C', hC'⟩ := hG.2 k
  refine ⟨C + C', fun a x => ?_⟩
  have h := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) (x := x)
    (contDiff_nat_of_top (hF.1 a) k).contDiffAt (contDiff_nat_of_top (hG.1 a) k).contDiffAt
  show ‖iteratedFDeriv ℝ k (F a + G a) x‖ ≤ C + C'
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (hC a x) (hC' a x))

theorem UnifBdd.neg {F : ι → Vec d → ℝ} (hF : UnifBdd F) : UnifBdd (fun a x => -F a x) := by
  refine ⟨fun a => (hF.1 a).neg, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hF.2 k
  refine ⟨C, fun a x => ?_⟩
  show ‖iteratedFDeriv ℝ k (-F a) x‖ ≤ C
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact hC a x

theorem UnifBdd.sub {F G : ι → Vec d → ℝ} (hF : UnifBdd F) (hG : UnifBdd G) :
    UnifBdd (fun a x => F a x - G a x) :=
  (hF.add hG.neg).congr fun a x => (sub_eq_add_neg _ _).symm

theorem UnifBdd.mul {F G : ι → Vec d → ℝ} (hF : UnifBdd F) (hG : UnifBdd G) :
    UnifBdd (fun a x => F a x * G a x) := by
  refine ⟨fun a => (hF.1 a).mul (hG.1 a), fun k => ?_⟩
  choose C hC using hF.2
  choose C' hC' using hG.2
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |C i| * |C' (k - i)|, fun a x => ?_⟩
  have h := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hF.1 a) (hG.1 a) x (n := k)
    (by exact_mod_cast le_top)
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 : ‖iteratedFDeriv ℝ i (F a) x‖ ≤ |C i| := (hC i a x).trans (le_abs_self _)
  have h2 : ‖iteratedFDeriv ℝ (k - i) (G a) x‖ ≤ |C' (k - i)| :=
    (hC' (k - i) a x).trans (le_abs_self _)
  have hc : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
    (mul_nonneg hc (abs_nonneg _))

theorem UnifBdd.const_mul (c : ℝ) {F : ι → Vec d → ℝ} (hF : UnifBdd F) :
    UnifBdd (fun a x => c * F a x) :=
  (unifBdd_const c).mul hF

theorem UnifBdd.sum {κ : Type*} (H : κ → ι → Vec d → ℝ) (hH : ∀ j, UnifBdd (H j))
    (s : Finset κ) : UnifBdd (fun a x => ∑ j ∈ s, H j a x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (unifBdd_const (0 : ℝ)).congr fun a x => by simp
  | insert j s hj ih =>
    exact ((hH j).add ih).congr fun a x => by rw [Finset.sum_insert hj]

theorem UnifBdd.comp_Icc {F : ι → Vec d → ℝ} (hF : UnifBdd F) {h : ℝ → ℝ} {lo hi : ℝ}
    (hlh : lo < hi) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h (Icc lo hi))
    (hr : ∀ a x, F a x ∈ Icc lo hi) : UnifBdd (fun a x => h (F a x)) := by
  refine ⟨fun a => ?_, fun k => ?_⟩
  · exact hh.comp_contDiff (hF.1 a) (hr a)
  · have hB : ∀ i : ℕ, ∃ B : ℝ, ∀ y ∈ Icc lo hi, ‖iteratedFDerivWithin ℝ i h (Icc lo hi) y‖ ≤ B :=
      fun i => isCompact_Icc.exists_bound_of_continuousOn
        (hh.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) (uniqueDiffOn_Icc hlh))
    choose B hB using hB
    choose M hM using hF.2
    let C : ℝ := ∑ i ∈ Finset.range (k + 1), |B i|
    let D : ℝ := 1 + ∑ i ∈ Finset.range (k + 1), |M i|
    have hD1 : 1 ≤ D := by
      have : 0 ≤ ∑ i ∈ Finset.range (k + 1), |M i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      simp only [D]
      linarith
    refine ⟨k ! * C * D ^ k, fun a x => ?_⟩
    have hC : ∀ i, i ≤ k →
        ‖iteratedFDerivWithin ℝ i h (Icc lo hi) (F a x)‖ ≤ C := by
      intro i hi
      refine (hB i _ (hr a x)).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun i => |B i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i (F a) x‖ ≤ D ^ i := by
      intro i h1 hi
      have h2 : ‖iteratedFDeriv ℝ i (F a) x‖ ≤ D := by
        refine (hM i a x).trans ((le_abs_self _).trans ?_)
        have := Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
        simp only [D]
        linarith
      exact h2.trans (le_self_pow₀ hD1 (by omega))
    have := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) (g := h) (f := F a) (n := k)
      (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) (t := Icc lo hi)
      (by rintro _ ⟨y, rfl⟩; exact hr a y) (uniqueDiffOn_Icc hlh) hh (hF.1 a)
      (by exact_mod_cast le_top) x hC hD
    exact this

theorem UnifBdd.inv_Icc {F : ι → Vec d → ℝ} (hF : UnifBdd F) {lo hi : ℝ} (hlo : 0 < lo)
    (hlh : lo < hi) (hr : ∀ a x, F a x ∈ Icc lo hi) : UnifBdd (fun a x => (F a x)⁻¹) :=
  hF.comp_Icc (h := fun t => t⁻¹) hlh
    ((contDiffOn_inv ℝ).mono fun y hy => (lt_of_lt_of_le hlo hy.1).ne') hr

theorem UnifBdd.log_Icc {F : ι → Vec d → ℝ} (hF : UnifBdd F) {lo hi : ℝ} (hlo : 0 < lo)
    (hlh : lo < hi) (hr : ∀ a x, F a x ∈ Icc lo hi) : UnifBdd (fun a x => Real.log (F a x)) :=
  hF.comp_Icc (h := Real.log) hlh
    (Real.contDiffOn_log.mono fun y hy => (lt_of_lt_of_le hlo hy.1).ne') hr

end Algebra

section Coordinate

variable {ι : Type*} {d : ℕ}

/-- Quantitative form: bounds `C l` on every iterated coordinate derivative of one smooth function
give an operator-norm bound on its `k`-th Fréchet derivative depending only on `C` and `k`. -/
theorem norm_iteratedFDeriv_le_of_coordinate {f : Vec d → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (C : List (Fin d) → ℝ) (hC : ∀ l x, |iteratedCoordinateDerivative l f x| ≤ C l) (k : ℕ)
    (x : Vec d) : ‖iteratedFDeriv ℝ k f x‖ ≤ ∑ dirs : Fin k → Fin d, |C (List.ofFn dirs)| := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun v => ?_
  rw [Real.norm_eq_abs, multilinear_expand]
  calc
    |∑ dirs : Fin k → Fin d,
        (∏ j, v j (dirs j)) * iteratedFDeriv ℝ k f x (fun j => unitVector (dirs j))| ≤
        ∑ dirs : Fin k → Fin d,
          |(∏ j, v j (dirs j)) * iteratedFDeriv ℝ k f x (fun j => unitVector (dirs j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ dirs : Fin k → Fin d, (∏ j, ‖v j‖) * |C (List.ofFn dirs)| := by
      apply Finset.sum_le_sum
      intro dirs _
      rw [abs_mul, Finset.abs_prod]
      have hp : (∏ j, |v j (dirs j)|) ≤ ∏ j, ‖v j‖ :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
          (fun j _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm (v j) (dirs j))
      have hT : |iteratedFDeriv ℝ k f x (fun j => unitVector (dirs j))| ≤
          |C (List.ofFn dirs)| := by
        rw [iteratedFDeriv_basis hs]
        exact (hC _ x).trans (le_abs_self _)
      exact mul_le_mul hp hT (abs_nonneg _) (Finset.prod_nonneg (fun j _ => norm_nonneg _))
    _ = (∑ dirs : Fin k → Fin d, |C (List.ofFn dirs)|) * ∏ j, ‖v j‖ := by
      rw [← Finset.mul_sum, mul_comm]

/-- Uniform bounds on every iterated coordinate derivative give uniform operator-norm bounds. -/
theorem UnifBdd.of_coordinate {F : ι → Vec d → ℝ} (hs : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (F a))
    (hb : ∀ l : List (Fin d), ∃ C : ℝ, ∀ a x, |iteratedCoordinateDerivative l (F a) x| ≤ C) :
    UnifBdd F := by
  refine ⟨hs, fun k => ?_⟩
  choose C hC using hb
  exact ⟨∑ dirs : Fin k → Fin d, |C (List.ofFn dirs)|, fun a x =>
    norm_iteratedFDeriv_le_of_coordinate (hs a) C (fun l x => hC l a x) k x⟩

/-- Operator-norm bounds give bounds on every iterated coordinate derivative. -/
theorem UnifBdd.coordinate {F : ι → Vec d → ℝ} (hF : UnifBdd F) (l : List (Fin d)) :
    ∃ C : ℝ, ∀ a x, |iteratedCoordinateDerivative l (F a) x| ≤ C := by
  obtain ⟨C, hC⟩ := hF.2 l.length
  refine ⟨C, fun a x => ?_⟩
  have hb := iteratedFDeriv_basis (hF.1 a) l.length l.get x
  rw [List.ofFn_get] at hb
  rw [← hb, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have hprod : ∏ j, ‖unitVector (l.get j)‖ ≤ 1 :=
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_unitVector_le_one _)).trans
      (by simp)
  calc ‖iteratedFDeriv ℝ l.length (F a) x‖ * ∏ j, ‖unitVector (l.get j)‖
      ≤ ‖iteratedFDeriv ℝ l.length (F a) x‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ C := by rw [mul_one]; exact hC a x

theorem iteratedCoordinateDerivative_append_single (l : List (Fin d)) (j : Fin d)
    (f : Vec d → ℝ) :
    iteratedCoordinateDerivative l (coordinateDerivative j f) =
      iteratedCoordinateDerivative (l ++ [j]) f := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, iteratedCoordinateDerivative_cons, ih]

/-- A coordinate derivative of a uniformly bounded family is uniformly bounded. -/
theorem UnifBdd.coordDeriv {F : ι → Vec d → ℝ} (hF : UnifBdd F) (j : Fin d) :
    UnifBdd (fun a => coordinateDerivative j (F a)) := by
  refine UnifBdd.of_coordinate (fun a => ?_) fun l => ?_
  · exact contDiff_iteratedCoordinateDerivative (F a) (hF.1 a) [j]
  · obtain ⟨C, hC⟩ := hF.coordinate (l ++ [j])
    refine ⟨C, fun a x => ?_⟩
    rw [iteratedCoordinateDerivative_append_single]
    exact hC a x

/-- Operator-norm bounds for a family give Euclidean multilinear bounds. -/
theorem UnifBdd.euclid_bound {F : ι → Vec d → ℝ} (hF : UnifBdd F) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x (v : Fin k → Vec d),
      |iteratedFDeriv ℝ k (F a) x v| ≤ C * ∏ j, euclideanNorm (v j) := by
  obtain ⟨C, hC⟩ := hF.2 k
  refine ⟨|C|, abs_nonneg _, fun a x v => ?_⟩
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have hp : ∏ j, ‖v j‖ ≤ ∏ j, euclideanNorm (v j) :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_le_euclideanNorm _)
  exact mul_le_mul ((hC a x).trans (le_abs_self _)) hp (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (abs_nonneg _)

end Coordinate

end EinsteinFull.Calculus.S1
