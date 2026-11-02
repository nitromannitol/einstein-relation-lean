import EinsteinFull.Calculus.S4SmoothGeneratorSupport

/-!
# Continuity and boundedness of the generators on test functions (smooth regular environments)

For a smooth regular environment and `f ∈ C_c^∞`, `reducedGenerator i ω lam f` and
`physicalGenerator i ω lam f` are continuous and bounded.  This is the input for the
change of variables and the optional stopping argument of the time change.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace EinsteinFull
open EinsteinRelation

theorem contDiff_two_of_top {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ 2 f := by
  first
    | exact hf.of_le (by exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
    | exact hf.of_le (by simp)
    | exact hf.of_le (by norm_cast; exact le_top)
    | exact hf.of_le (WithTop.coe_le_coe.2 le_top)

theorem continuous_fderiv_apply_second {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    (i j : Fin d) :
    Continuous fun x => fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) := by
  have h1 : ContDiff ℝ 1 (fun y => fderiv ℝ f y (unitVector j)) :=
    (hf.fderiv_right (le_of_eq one_add_one_eq_two)).clm_apply contDiff_const
  exact (h1.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_fderiv_apply_first {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    (j : Fin d) : Continuous fun x => fderiv ℝ f x (unitVector j) :=
  (hf.continuous_fderiv two_ne_zero).clm_apply continuous_const

theorem continuous_svGenerator {d : ℕ} (A : Vec d → Mat d) (b : Vec d → Vec d)
    (hA : ∀ i j, Continuous fun x => A x i j) (hb : ∀ k, Continuous fun x => b x k)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (External.Draft.svGenerator A b f) := by
  unfold External.Draft.svGenerator
  refine Continuous.add ?_ ?_
  · refine continuous_const.mul ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    first
      | exact (hA i j).fun_mul (continuous_fderiv_apply_second hf i j)
      | exact (hA i j).mul (continuous_fderiv_apply_second hf i j)
  · refine continuous_finsetSum _ fun i _ => ?_
    first
      | exact (hb i).fun_mul (continuous_fderiv_apply_first hf i)
      | exact (hb i).mul (continuous_fderiv_apply_first hf i)

theorem bounded_svGenerator {d : ℕ} (A : Vec d → Mat d) (b : Vec d → Vec d) {M1 M2 : ℝ}
    (hA : ∀ x i j, |A x i j| ≤ M1) (hb : ∀ x k, |b x k| ≤ M2)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x, |External.Draft.svGenerator A b f x| ≤ C := by
  have h1 : ∀ j : Fin d, ∃ B : ℝ, ∀ x, ‖fderiv ℝ f x (unitVector j)‖ ≤ B := fun j =>
    (continuous_fderiv_apply_first hf j).bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j))
  have h2 : ∀ i j : Fin d, ∃ B : ℝ,
      ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)‖ ≤ B :=
    fun i j =>
    (continuous_fderiv_apply_second hf i j).bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ)
        (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j)) (unitVector i))
  choose B1 hB1 using h1
  choose B2 hB2 using h2
  refine ⟨(1 / 2 : ℝ) * ∑ i, ∑ j, M1 * B2 i j + ∑ i, M2 * B1 i, fun x => ?_⟩
  unfold External.Draft.svGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hA x i j) (by simpa only [Real.norm_eq_abs] using hB2 i j x)
      (abs_nonneg _) ((abs_nonneg _).trans (hA x i j))
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hb x i) (by simpa only [Real.norm_eq_abs] using hB1 i x)
      (abs_nonneg _) ((abs_nonneg _).trans (hb x i))

theorem continuous_forcedDrift_apply {d : ℕ} {ω : FieldPair d} (hs : IsSmoothFieldPair ω)
    (i : Fin d) (lam : ℝ) (k : Fin d) :
    Continuous fun x => forcedDrift (reducedCoefficient ω) i lam x k := by
  have e : (fun x => forcedDrift (reducedCoefficient ω) i lam x k) = fun x =>
      (1 / 2 : ℝ) * ∑ l, fderiv ℝ (fun z => reducedCoefficient ω z l k) x (unitVector l) +
        lam * reducedCoefficient ω x k i := by
    funext x
    simp only [forcedDrift, matrixDivDrift, coordinateDerivative]
    congr 2
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  rw [e]
  refine Continuous.add (continuous_const.mul ?_) (continuous_const.mul ?_)
  · refine continuous_finsetSum _ fun l _ => ?_
    exact ((contDiff_reducedCoefficient_entry hs l k).continuous_fderiv (by simp)).clm_apply
      continuous_const
  · exact ((continuous_reducedCoefficient ω).matrix_elem k i)

theorem continuous_reducedGenerator_apply {d : ℕ} {ω : FieldPair d}
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (reducedGenerator i ω lam f) := by
  have hf2 := contDiff_two_of_top hf
  have e : reducedGenerator i ω lam f = External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) f :=
    funext fun x => reducedGenerator_eq_svGenerator hs i lam hf2 x
  rw [e]
  exact continuous_svGenerator _ _ (fun a b => (continuous_reducedCoefficient ω).matrix_elem a b)
    (continuous_forcedDrift_apply hs i lam) hf2

theorem bounded_reducedGenerator_apply {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x, |reducedGenerator i ω lam f x| ≤ C := by
  have hf2 := contDiff_two_of_top hf
  obtain ⟨_, _, ⟨Ma, hMa⟩, _, _, ⟨Mb, hMb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  obtain ⟨C, hC⟩ := bounded_svGenerator (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i lam) hMa hMb hf2 hc
  refine ⟨C, fun x => ?_⟩
  rw [reducedGenerator_eq_svGenerator hs i lam hf2 x]
  exact hC x

theorem physicalGenerator_eq_inv_mul {d : ℕ} (ω : FieldPair d) (i : Fin d) (lam : ℝ)
    (f : Vec d → ℝ) (x : Vec d) :
    physicalGenerator i ω lam f x =
      (clockDensity ω x)⁻¹ * reducedGenerator i ω lam f x := by
  rw [← clockDensity_mul_physicalGenerator, ← mul_assoc,
    inv_mul_cancel₀ (clockDensity_pos ω x).ne', one_mul]

theorem continuous_physicalGenerator_apply {d : ℕ} {ω : FieldPair d}
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (physicalGenerator i ω lam f) := by
  have e : physicalGenerator i ω lam f =
      fun x => (clockDensity ω x)⁻¹ * reducedGenerator i ω lam f x :=
    funext fun x => physicalGenerator_eq_inv_mul ω i lam f x
  rw [e]
  have hμ : Continuous (clockDensity ω) := (reduce ω).2.continuous
  exact (hμ.inv₀ fun x => (clockDensity_pos ω x).ne').mul
    (continuous_reducedGenerator_apply hs i lam hf)

theorem bounded_physicalGenerator_apply {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x, |physicalGenerator i ω lam f x| ≤ C := by
  obtain ⟨C, hC⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam hf hc
  refine ⟨Real.exp (2 * Λ₀) * C, fun x => ?_⟩
  rw [physicalGenerator_eq_inv_mul, abs_mul]
  have hinv : (clockDensity ω x)⁻¹ = Real.exp (2 * ω.2 x) := by
    rw [clockDensity, ← Real.exp_neg]
    congr 1
    ring
  have h1 : |(clockDensity ω x)⁻¹| ≤ Real.exp (2 * Λ₀) := by
    rw [hinv, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by have := (abs_le.1 (hω.2.1 x)).2; linarith)
  exact mul_le_mul h1 (hC x) (abs_nonneg _) (Real.exp_pos _).le

end EinsteinFull
