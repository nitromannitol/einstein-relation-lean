import EinsteinFull.Calculus.S4GeneratorRegularitySupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Carré du champ of the textbook operator and rescaled cutoffs

* `svGenerator_sq_sub`: `L (u²) - 2 u L u = Σᵢⱼ Aᵢⱼ ∂ᵢu ∂ⱼu` for `u ∈ C²`;
* a cutoff family `χ_R f` whose first partial derivatives are bounded uniformly in `R ≥ 1`
  when `f` has bounded first partials and at most linear growth.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace EinsteinFull
open EinsteinRelation

theorem fderiv_sq_apply {d : ℕ} {u : Vec d → ℝ} (hd : Differentiable ℝ u) (z v : Vec d) :
    fderiv ℝ (fun w => u w ^ 2) z v = 2 * u z * fderiv ℝ u z v := by
  have h : HasFDerivAt (fun w => u w ^ 2) ((2 * u z) • fderiv ℝ u z) z :=
    ((hasDerivAt_pow 2 (u z)).comp_hasFDerivAt z (hd z).hasFDerivAt).congr_fderiv (by simp)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem fderiv_sq_apply_second {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (y : Vec d)
    (i j : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => u w ^ 2) z (unitVector j)) y (unitVector i) =
      2 * (fderiv ℝ u y (unitVector i) * fderiv ℝ u y (unitVector j)) +
        2 * u y * fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y (unitVector i) := by
  have hd : Differentiable ℝ u := hu.differentiable (by first | exact one_le_two | norm_num)
  have hg1 : ContDiff ℝ 1 (fun z => fderiv ℝ u z (unitVector j)) :=
    (hu.fderiv_right (le_of_eq one_add_one_eq_two)).clm_apply contDiff_const
  have hgd : Differentiable ℝ (fun z => fderiv ℝ u z (unitVector j)) :=
    hg1.differentiable one_ne_zero
  have e : (fun z => fderiv ℝ (fun w => u w ^ 2) z (unitVector j)) =
      fun z => 2 * u z * fderiv ℝ u z (unitVector j) :=
    funext fun z => fderiv_sq_apply hd z _
  have hh := (((hd y).hasFDerivAt.const_mul (2 : ℝ)).mul (hgd y).hasFDerivAt)
  have key : fderiv ℝ (fun z => 2 * u z * fderiv ℝ u z (unitVector j)) y = _ :=
    HasFDerivAt.fderiv hh
  rw [e, key]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The carré du champ of the textbook operator. -/
theorem svGenerator_sq_sub {d : ℕ} (A : Vec d → Mat d) (b : Vec d → Vec d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ 2 u) (y : Vec d) :
    External.Draft.svGenerator A b (fun z => u z ^ 2) y -
        2 * u y * External.Draft.svGenerator A b u y =
      ∑ i, ∑ j, A y i j * (fderiv ℝ u y (unitVector i) * fderiv ℝ u y (unitVector j)) := by
  have hd : Differentiable ℝ u := hu.differentiable (by first | exact one_le_two | norm_num)
  unfold External.Draft.svGenerator
  simp only [fderiv_sq_apply_second hu]
  simp only [fderiv_sq_apply hd]
  have e1 : ∀ i j, A y i j * (2 * (fderiv ℝ u y (unitVector i) * fderiv ℝ u y (unitVector j)) +
      2 * u y * fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y (unitVector i)) =
      2 * (A y i j * (fderiv ℝ u y (unitVector i) * fderiv ℝ u y (unitVector j))) +
      2 * u y * (A y i j * fderiv ℝ (fun z => fderiv ℝ u z (unitVector j)) y (unitVector i)) :=
    fun i j => by ring
  have e2 : ∀ i, b y i * (2 * u y * fderiv ℝ u y (unitVector i)) =
      2 * u y * (b y i * fderiv ℝ u y (unitVector i)) := fun i => by ring
  simp only [e1, e2, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem carre_du_champ_le {d : ℕ} {A : Vec d → Mat d} {M1 G : ℝ}
    (hA : ∀ x i j, |A x i j| ≤ M1) (g : Vec d) (hg : ∀ i, |g i| ≤ G) (y : Vec d) :
    ∑ i, ∑ j, A y i j * (g i * g j) ≤ (d : ℝ) * d * (M1 * (G * G)) := by
  calc ∑ i, ∑ j, A y i j * (g i * g j) ≤ ∑ i : Fin d, ∑ j : Fin d, M1 * (G * G) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hA y i j) (mul_le_mul (hg i) (hg j) (abs_nonneg _)
          ((abs_nonneg _).trans (hg i))) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          ((abs_nonneg _).trans (hA y i j))
    _ = (d : ℝ) * d * (M1 * (G * G)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Rescaled cutoffs -/

theorem exists_cutoff (d : ℕ) : ∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
    (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y, ‖y‖ ≤ 1 → χ y = 1) ∧ (∀ y, 2 ≤ ‖y‖ → χ y = 0) := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, fun y => ⟨b.nonneg, b.le_one⟩,
    fun y hy => b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hy),
    fun y hy => b.zero_of_le_dist ?_⟩
  rw [dist_zero_right]
  exact hy

theorem fderiv_cutoff_eq_zero {d : ℕ} {χ : Vec d → ℝ} (hχ0 : ∀ y, 2 ≤ ‖y‖ → χ y = 0) {w : Vec d}
    (hw : 2 < ‖w‖) : fderiv ℝ χ w = 0 := by
  have hev : χ =ᶠ[𝓝 w] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with z hz
    exact hχ0 z (le_of_lt hz)
  rw [hev.fderiv_eq]
  simp

theorem exists_cutoff_deriv_bound {d : ℕ} {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) : ∃ c : ℝ, ∀ w i, |fderiv ℝ χ w (unitVector i)| ≤ c := by
  have h1 : ∀ j : Fin d, ∃ B : ℝ, ∀ x, ‖fderiv ℝ χ x (unitVector j)‖ ≤ B := fun j =>
    (continuous_fderiv_apply_first (contDiff_two_of_top hχ) j).bounded_above_of_compact_support
      (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j))
  choose B hB using h1
  have hB0 : ∀ j, 0 ≤ B j := fun j => (norm_nonneg _).trans (hB j 0)
  refine ⟨∑ j, B j, fun w i => ?_⟩
  have := hB i w
  rw [Real.norm_eq_abs] at this
  exact this.trans (Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_univ i))

/-- The rescaled cutoff `χ(R⁻¹ y) f(y)`. -/
noncomputable def cutoffFn {d : ℕ} (χ : Vec d → ℝ) (R : ℝ) (f : Vec d → ℝ) : Vec d → ℝ :=
  fun y => χ (R⁻¹ • y) * f y

theorem contDiff_cutoffFn {d : ℕ} {χ f : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoffFn χ R f) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => χ (R⁻¹ • y)) :=
    hχ.comp (contDiff_const_smul R⁻¹)
  first
    | exact h1.mul hf
    | exact h1.fun_mul hf

theorem norm_inv_smul_le {d : ℕ} {R : ℝ} (hR : 0 < R) (y : Vec d) :
    ‖R⁻¹ • y‖ = R⁻¹ * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]

theorem hasCompactSupport_cutoffFn {d : ℕ} {χ : Vec d → ℝ} (f : Vec d → ℝ) {R : ℝ} (hR : 0 < R)
    (hχ0 : ∀ y, 2 ≤ ‖y‖ → χ y = 0) : HasCompactSupport (cutoffFn χ R f) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) (2 * R)) fun y hy => ?_
  have h1 : 2 * R < ‖y‖ := by
    by_contra h
    exact hy (mem_closedBall_zero_iff.2 (not_lt.1 h))
  have h2 : 2 ≤ ‖R⁻¹ • y‖ := by
    rw [norm_inv_smul_le hR, ← div_eq_inv_mul, le_div_iff₀ hR]
    linarith
  simp [cutoffFn, hχ0 _ h2]

theorem cutoffFn_eq {d : ℕ} {χ : Vec d → ℝ} (f : Vec d → ℝ) {R : ℝ} (hR : 0 < R)
    (hχ1 : ∀ y, ‖y‖ ≤ 1 → χ y = 1) {y : Vec d} (hy : ‖y‖ ≤ R) : cutoffFn χ R f y = f y := by
  have h : ‖R⁻¹ • y‖ ≤ 1 := by
    rw [norm_inv_smul_le hR, ← div_eq_inv_mul, div_le_one hR]
    exact hy
  simp [cutoffFn, hχ1 _ h]

theorem cutoffFn_eventuallyEq {d : ℕ} {χ : Vec d → ℝ} (f : Vec d → ℝ) {R : ℝ} (hR : 0 < R)
    (hχ1 : ∀ y, ‖y‖ ≤ 1 → χ y = 1) {y : Vec d} (hy : ‖y‖ < R) :
    cutoffFn χ R f =ᶠ[𝓝 y] f := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
  exact cutoffFn_eq f hR hχ1 (le_of_lt hz)

theorem fderiv_cutoffFn_apply {d : ℕ} {χ f : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (R : ℝ) (y : Vec d) (i : Fin d) :
    fderiv ℝ (cutoffFn χ R f) y (unitVector i) =
      χ (R⁻¹ • y) * fderiv ℝ f y (unitVector i) +
        f y * (R⁻¹ * fderiv ℝ χ (R⁻¹ • y) (unitVector i)) := by
  have hχd : DifferentiableAt ℝ χ (R⁻¹ • y) := (hχ.differentiable (by simp)) _
  have h1 : HasFDerivAt (fun z : Vec d => χ (R⁻¹ • z))
      ((fderiv ℝ χ (R⁻¹ • y)).comp (R⁻¹ • ContinuousLinearMap.id ℝ (Vec d))) y :=
    hχd.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul R⁻¹)
  have h2 := h1.mul ((hf.differentiable (by simp)) y).hasFDerivAt
  have key : fderiv ℝ (cutoffFn χ R f) y = _ := HasFDerivAt.fderiv h2
  rw [key]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul, map_smul]

/-- Uniform bound on the first partials of the cutoffs. -/
theorem abs_fderiv_cutoffFn_le {d : ℕ} {χ f : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hχ0 : ∀ y, 2 ≤ ‖y‖ → χ y = 0) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    {G0 a b c : ℝ} (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0)
    (hgrow : ∀ y, |f y| ≤ a + b * ‖y‖) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : ∀ w i, |fderiv ℝ χ w (unitVector i)| ≤ c) {R : ℝ} (hR : 1 ≤ R) (y : Vec d)
    (i : Fin d) :
    |fderiv ℝ (cutoffFn χ R f) y (unitVector i)| ≤ G0 + (a + 2 * b) * c := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hs0 : 0 < R⁻¹ := inv_pos.2 hR0
  have hs1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hRs : R * R⁻¹ = 1 := mul_inv_cancel₀ hR0.ne'
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0 i)
  have hG00 : 0 ≤ G0 := (abs_nonneg _).trans (hG0 y i)
  rw [fderiv_cutoffFn_apply hχ hf]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (hχ01 _).1]
    calc χ (R⁻¹ • y) * |fderiv ℝ f y (unitVector i)| ≤ 1 * G0 :=
          mul_le_mul (hχ01 _).2 (hG0 y i) (abs_nonneg _) zero_le_one
      _ = G0 := one_mul _
  · rw [abs_mul, abs_mul, abs_of_pos hs0]
    by_cases hy : 2 < ‖R⁻¹ • y‖
    · rw [fderiv_cutoff_eq_zero hχ0 hy]
      simp only [ContinuousLinearMap.zero_apply, abs_zero, mul_zero]
      positivity
    · have hy' : ‖y‖ ≤ 2 * R := by
        have h := not_lt.1 hy
        rw [norm_inv_smul_le hR0, ← div_eq_inv_mul, div_le_iff₀ hR0] at h
        linarith
      have h1 : (a + b * ‖y‖) * R⁻¹ ≤ a + 2 * b := by
        have ha' : a * R⁻¹ ≤ a * 1 := mul_le_mul_of_nonneg_left hs1 ha
        have hb' : b * ‖y‖ * R⁻¹ ≤ b * (2 * R) * R⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy' hb) hs0.le
        have hb'' : b * (2 * R) * R⁻¹ = 2 * b := by
          calc b * (2 * R) * R⁻¹ = 2 * b * (R * R⁻¹) := by ring
            _ = 2 * b := by rw [hRs]; ring
        nlinarith
      calc |f y| * (R⁻¹ * |fderiv ℝ χ (R⁻¹ • y) (unitVector i)|)
          ≤ (a + b * ‖y‖) * (R⁻¹ * c) :=
            mul_le_mul (hgrow y) (mul_le_mul_of_nonneg_left (hc _ _) hs0.le)
              (mul_nonneg hs0.le (abs_nonneg _)) (by positivity)
        _ = (a + b * ‖y‖) * R⁻¹ * c := by ring
        _ ≤ (a + 2 * b) * c := mul_le_mul_of_nonneg_right h1 hc0

end EinsteinFull
