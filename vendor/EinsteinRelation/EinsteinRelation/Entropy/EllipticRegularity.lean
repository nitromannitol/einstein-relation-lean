import EinsteinRelation.Entropy.DivergenceSecondAssertion
import EinsteinRelation.Entropy.DynkinFromFukushima
import EinsteinRelation.Entropy.WeakResolventFromDynkin
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! # Elliptic regularity for the resolvent densities

Source: `paper/main.tex` 535-560 (Step 2 of Lemma 4.1), in the stationary form used by the operator
route to Lemma 4.1. An `L²` very weak
solution `ρ` of `μρ - L*ρ = f` with `f ∈ L²` has a weak horizontal gradient in `L²`. The proof
smooths `ρ`, controls the commutator of the smoothing with `L` without second derivatives, and
tests the smoothed equation with the smoothed density.

This file starts with the `L²` adjoint identity for horizontal smoothings.
-/

open MeasureTheory Filter
open scoped ENNReal Topology NNReal

noncomputable section

open EinsteinRelation.External.GantertSection7Support

namespace EinsteinRelation.Entropy

variable {d : ℕ}

/-! ## The `L²` adjoint identity -/

theorem memLp_comp_translate {Q : Measure (FieldPair d)} (hQ : IsStationary Q)
    {u : FieldPair d → ℝ} {q : ℝ≥0∞} (hu : MemLp u q Q) (y : Vec d) :
    MemLp (fun ω => u (translate y ω)) q Q := by
  have h : MemLp u q (Measure.map (translate y) Q) := by
    rw [hQ y]
    exact hu
  exact MemLp.comp_of_map h (Probability.measurable_translate y).aemeasurable

theorem integral_sq_comp_translate {Q : Measure (FieldPair d)} (hQ : IsStationary Q)
    {u : FieldPair d → ℝ} (hum : Measurable u) (y : Vec d) :
    ∫ ω, u (translate y ω) ^ 2 ∂Q = ∫ ω, u ω ^ 2 ∂Q :=
  Probability.integral_translate Q hQ y (fun η => u η ^ 2) (hum.pow_const 2)

/-- **The `L²` adjoint identity**: `E[(S_κ u) W] = E[u (S_κ̃ W)]` for `u, W ∈ L²` and an integrable
kernel `κ`, where `κ̃ = κ(-·)`. -/
theorem integral_horizontalMollify_mul_eq_L2 {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {κ : Vec d → ℝ} (hκm : Measurable κ) (hκi : Integrable κ)
    {u W : FieldPair d → ℝ} (hum : Measurable u) (hu : MemLp u 2 Q) (hWm : Measurable W)
    (hW : MemLp W 2 Q) :
    ∫ ω, horizontalMollify κ u ω * W ω ∂Q =
      ∫ ω, u ω * horizontalMollify (reflectKernel κ) W ω ∂Q := by
  have hT : Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
    Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hTn : Measurable (fun p : FieldPair d × Vec d => translate (-p.2) p.1) :=
    Probability.continuous_translate.measurable.comp (measurable_snd.neg.prodMk measurable_fst)
  set M : ℝ := ((∫ ω, u ω ^ 2 ∂Q) + ∫ ω, W ω ^ 2 ∂Q) / 2 with hMdef
  have hu2 : Integrable (fun ω => u ω ^ 2) Q := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mp hu
  have hW2 : Integrable (fun ω => W ω ^ 2) Q := (memLp_two_iff_integrable_sq hW.aestronglyMeasurable).mp hW
  -- `∫ |u ∘ τ_y| |W| ≤ M` for every `y`.
  have hbd : ∀ (y : Vec d) (V : FieldPair d → ℝ), Measurable V → MemLp V 2 Q →
      (∫ ω, V ω ^ 2 ∂Q) = ∫ ω, u ω ^ 2 ∂Q →
      ∫ ω, |V ω| * |W ω| ∂Q ≤ M := by
    intro y V hVm hV hVsq
    have hV2 : Integrable (fun ω => V ω ^ 2) Q := (memLp_two_iff_integrable_sq hV.aestronglyMeasurable).mp hV
    have hle : ∀ ω, |V ω| * |W ω| ≤ (V ω ^ 2 + W ω ^ 2) / 2 := fun ω => by
      have := two_mul_le_add_sq |V ω| |W ω|
      rw [sq_abs, sq_abs] at this
      linarith
    have hI : Integrable (fun ω => |V ω| * |W ω|) Q :=
      (hV.integrable_mul hW).abs.congr (ae_of_all _ fun ω => by
        show |V ω * W ω| = |V ω| * |W ω|
        exact abs_mul _ _)
    calc ∫ ω, |V ω| * |W ω| ∂Q ≤ ∫ ω, (V ω ^ 2 + W ω ^ 2) / 2 ∂Q :=
          integral_mono hI ((hV2.add hW2).div_const 2) hle
      _ = M := by
          rw [integral_div, integral_add hV2 hW2, hVsq]
  have hint1 : Integrable (fun p : FieldPair d × Vec d => κ p.2 * u (translate p.2 p.1) * W p.1)
      (Q.prod volume) := by
    have hmeas : Measurable (fun p : FieldPair d × Vec d => κ p.2 * u (translate p.2 p.1) * W p.1) :=
      ((hκm.comp measurable_snd).mul (hum.comp hT)).mul (hWm.comp measurable_fst)
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun y => ?_, ?_⟩
    · have h := ((memLp_comp_translate hQ hu y).integrable_mul hW).const_mul (κ y)
      refine h.congr (ae_of_all _ fun ω => ?_)
      simp only [Pi.mul_apply]
      ring
    · refine (hκi.norm.mul_const M).mono'
        (hmeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable)
        (ae_of_all _ fun y => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
      have e : (∫ ω, ‖κ y * u (translate y ω) * W ω‖ ∂Q) =
          ‖κ y‖ * ∫ ω, |u (translate y ω)| * |W ω| ∂Q := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only [norm_mul, Real.norm_eq_abs]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (hbd y _ (hum.comp (Probability.measurable_translate y))
        (memLp_comp_translate hQ hu y) (integral_sq_comp_translate hQ hum y)) (norm_nonneg _)
  have hint2 : Integrable (fun p : FieldPair d × Vec d => κ p.2 * W (translate (-p.2) p.1) * u p.1)
      (Q.prod volume) := by
    have hmeas : Measurable
        (fun p : FieldPair d × Vec d => κ p.2 * W (translate (-p.2) p.1) * u p.1) :=
      ((hκm.comp measurable_snd).mul (hWm.comp hTn)).mul (hum.comp measurable_fst)
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun y => ?_, ?_⟩
    · have h := ((memLp_comp_translate hQ hW (-y)).integrable_mul hu).const_mul (κ y)
      refine h.congr (ae_of_all _ fun ω => ?_)
      simp only [Pi.mul_apply]
      ring
    · set M' : ℝ := ((∫ ω, W ω ^ 2 ∂Q) + ∫ ω, u ω ^ 2 ∂Q) / 2 with hM'def
      refine (hκi.norm.mul_const M').mono'
        (hmeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable)
        (ae_of_all _ fun y => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
      have e : (∫ ω, ‖κ y * W (translate (-y) ω) * u ω‖ ∂Q) =
          ‖κ y‖ * ∫ ω, |W (translate (-y) ω)| * |u ω| ∂Q := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only [norm_mul, Real.norm_eq_abs]
        ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hW' := memLp_comp_translate hQ hW (-y)
      have hW'2 : Integrable (fun ω => W (translate (-y) ω) ^ 2) Q :=
        (memLp_two_iff_integrable_sq hW'.aestronglyMeasurable).mp hW'
      have hle : ∀ ω, |W (translate (-y) ω)| * |u ω| ≤ (W (translate (-y) ω) ^ 2 + u ω ^ 2) / 2 :=
        fun ω => by
          have := two_mul_le_add_sq |W (translate (-y) ω)| |u ω|
          rw [sq_abs, sq_abs] at this
          linarith
      have hI : Integrable (fun ω => |W (translate (-y) ω)| * |u ω|) Q :=
        (hW'.integrable_mul hu).abs.congr (ae_of_all _ fun ω => by
          show |W (translate (-y) ω) * u ω| = |W (translate (-y) ω)| * |u ω|
          exact abs_mul _ _)
      calc ∫ ω, |W (translate (-y) ω)| * |u ω| ∂Q ≤
            ∫ ω, (W (translate (-y) ω) ^ 2 + u ω ^ 2) / 2 ∂Q :=
            integral_mono hI ((hW'2.add hu2).div_const 2) hle
        _ = M' := by
            rw [integral_div, integral_add hW'2 hu2,
              integral_sq_comp_translate hQ hWm (-y)]
  -- The exchanges.
  have step1 : (∫ ω, horizontalMollify κ u ω * W ω ∂Q) =
      ∫ y, κ y * (∫ ω, u (translate y ω) * W ω ∂Q) := by
    have h1 : (fun ω => horizontalMollify κ u ω * W ω) =
        fun ω => ∫ y, κ y * u (translate y ω) * W ω := by
      funext ω
      unfold horizontalMollify
      rw [← integral_mul_const]
    rw [h1, integral_integral_swap hint1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show (∫ ω, κ y * u (translate y ω) * W ω ∂Q) = κ y * ∫ ω, u (translate y ω) * W ω ∂Q
    rw [← integral_const_mul]
    simp only [mul_assoc]
  have step2 : ∀ y : Vec d, (∫ ω, u (translate y ω) * W ω ∂Q) =
      ∫ ω, W (translate (-y) ω) * u ω ∂Q := by
    intro y
    have hcancel : ∀ ω : FieldPair d, translate (-y) (translate y ω) = ω := by
      intro ω
      rw [translate_add, neg_add_cancel, translate_zero]
    have hm : Measurable (fun η : FieldPair d => W (translate (-y) η) * u η) :=
      (hWm.comp (Probability.measurable_translate (-y))).mul hum
    have h := Probability.integral_translate Q hQ y (fun η => W (translate (-y) η) * u η) hm
    simp only [hcancel] at h
    rw [← h]
    exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  have step3 : (∫ ω, u ω * horizontalMollify (reflectKernel κ) W ω ∂Q) =
      ∫ y, κ y * (∫ ω, W (translate (-y) ω) * u ω ∂Q) := by
    have h1 : (fun ω => u ω * horizontalMollify (reflectKernel κ) W ω) =
        fun ω => ∫ y, κ y * W (translate (-y) ω) * u ω := by
      funext ω
      unfold horizontalMollify reflectKernel
      have e := integral_neg_eq_self (fun x : Vec d => κ (-x) * W (translate x ω))
        (volume : Measure (Vec d))
      simp only [neg_neg] at e
      rw [← e, mul_comm, ← integral_mul_const]
    rw [h1, integral_integral_swap hint2]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show (∫ ω, κ y * W (translate (-y) ω) * u ω ∂Q) = κ y * ∫ ω, W (translate (-y) ω) * u ω ∂Q
    rw [← integral_const_mul]
    simp only [mul_assoc]
  rw [step1, step3]
  exact integral_congr_ae (ae_of_all _ fun y => by simp only [step2 y])

/-! ## Smoothing commutes with horizontal derivatives of orbit tests -/

/-- `D_i (S_κ F) = S_κ (D_i F)` for an orbit test `F` and a smooth compactly supported kernel. -/
theorem horizontalDerivative_horizontalMollify_eq {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) (i : Fin d)
    (w : FieldPair d) :
    horizontalDerivative i (horizontalMollify κ F) w =
      horizontalMollify κ (horizontalDerivative i F) w := by
  obtain ⟨B, -, hB⟩ := hF.bound_orbit
  have hFb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M := ⟨B, fun ω => by simpa using hB ω 0⟩
  rw [Correctors.horizontalMollify_horizontalDerivative_formula hκ hκc hF.1 hFb i w]
  set g : Vec d → ℝ := orbit F w with hgdef
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := hF.2.1 w
  have hgd : Differentiable ℝ g := hgs.differentiable (by simp)
  have hκd : Differentiable ℝ κ := hκ.differentiable (by simp)
  obtain ⟨M1, -, hM1⟩ := hF.bound_derivative i
  have hκ1 : Continuous fun x => fderiv ℝ κ x (unitVector i) :=
    (hκ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hκ1c : HasCompactSupport fun x => fderiv ℝ κ x (unitVector i) :=
    hκc.fderiv_apply (𝕜 := ℝ) (unitVector i)
  have hgc : Continuous g := hgs.continuous
  have hg1c : Continuous fun x => fderiv ℝ g x (unitVector i) :=
    (hgs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI1 : Integrable (fun x => fderiv ℝ κ x (unitVector i) * g x) :=
    (hκ1.mul hgc).integrable_of_hasCompactSupport (hκ1c.mul_right)
  have hI2 : Integrable (fun x => κ x * fderiv ℝ g x (unitVector i)) :=
    (hκ.continuous.mul hg1c).integrable_of_hasCompactSupport (hκc.mul_right)
  have hI3 : Integrable (fun x => κ x * g x) :=
    (hκ.continuous.mul hgc).integrable_of_hasCompactSupport (hκc.mul_right)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vec d)))
    hI1 hI2 hI3 (fun x _ => hκd x) (fun x _ => hgd x)
  unfold horizontalMollify
  have e1 : (fun x => κ x * horizontalDerivative i F (translate x w)) =
      fun x => κ x * fderiv ℝ g x (unitVector i) := by
    funext x
    rw [horizontalDerivative_translate]
    rfl
  rw [e1, hibp]
  rfl

/-! ## The commutator of the smoothing with the generator -/

/-- Integration by parts in the orbit variable for the second-derivative term of the commutator:
`∫ κ (A(0) - A) ∂_k ψ = ∫ (-∂_k κ (A(0) - A) + κ ∂_k A) ψ` for a Lipschitz bounded `A`. -/
theorem integral_kernel_coeff_deriv {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) {A : Vec d → ℝ} {LA : ℝ≥0} {BA : ℝ} (hA : LipschitzWith LA A)
    (hAB : ∀ x, |A x| ≤ BA) {ψ : Vec d → ℝ} {Lψ : ℝ≥0} (hψ : LipschitzWith Lψ ψ)
    (hψd : Differentiable ℝ ψ) (k : Fin d) :
    ∫ x, κ x * (A 0 - A x) * fderiv ℝ ψ x (unitVector k) =
      ∫ x, (-(coordinateDerivative k κ x * (A 0 - A x)) + κ x * fderiv ℝ A x (unitVector k)) *
        ψ x := by
  obtain ⟨Lκ, hLκ⟩ := hκ.lipschitzWith_of_hasCompactSupport hκc (by simp) (𝕂 := ℝ)
  obtain ⟨Bκ, hBκ⟩ := hκc.exists_bound_of_continuous hκ.continuous
  have hA0 : LipschitzWith LA fun x => A 0 - A x := by
    have h := (LipschitzWith.const (A 0)).sub hA
    simpa using h
  have hA0B : ∀ x, |A 0 - A x| ≤ BA + BA := fun x =>
    (abs_sub _ _).trans (add_le_add (hAB 0) (hAB x))
  have hφ := lipschitzWith_mul_of_bounded hLκ hA0 (fun x => by
    rw [← Real.norm_eq_abs]; exact hBκ x) hA0B
  have hφc : HasCompactSupport fun x => κ x * (A 0 - A x) := hκc.mul_right
  have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Vec d))) hψ hφ hφc
    (unitVector k)
  have hL : (∫ x, lineDeriv ℝ ψ x (unitVector k) * (κ x * (A 0 - A x))) =
      ∫ x, κ x * (A 0 - A x) * fderiv ℝ ψ x (unitVector k) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show lineDeriv ℝ ψ x (unitVector k) * (κ x * (A 0 - A x)) =
      κ x * (A 0 - A x) * fderiv ℝ ψ x (unitVector k)
    rw [(hψd x).lineDeriv_eq_fderiv]
    ring
  have hR : (∫ x, lineDeriv ℝ (fun x => κ x * (A 0 - A x)) x (-unitVector k) * ψ x) =
      ∫ x, (-(coordinateDerivative k κ x * (A 0 - A x)) + κ x * fderiv ℝ A x (unitVector k)) *
        ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [hA.ae_differentiableAt (μ := (volume : Measure (Vec d)))] with x hx
    have hκd : DifferentiableAt ℝ κ x := (hκ.differentiable (by simp)) x
    have hfd : HasFDerivAt (fun x => κ x * (A 0 - A x))
        (κ x • (-fderiv ℝ A x) + (A 0 - A x) • fderiv ℝ κ x) x :=
      hκd.hasFDerivAt.mul ((hasFDerivAt_const (A 0) x).sub hx.hasFDerivAt |>.congr_fderiv
        (by simp))
    rw [hfd.differentiableAt.lineDeriv_eq_fderiv, hfd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.neg_apply, map_neg, coordinateDerivative]
    ring
  rw [← hL, h, hR]

/-- The kernel of the commutator `L S_κ - S_κ L`, acting on `D_j F`. -/
def commKernel (hd : 2 ≤ d) (lam : ℝ) (κ : Vec d → ℝ) (w : FieldPair d) (j : Fin d)
    (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, (κ x * fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) -
      coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) +
    lam * (κ x * (w.1 0 j (firstCoordinateIndex hd) - w.1 x j (firstCoordinateIndex hd)))

/-- The commutator operator, acting on a vector field `V` (for an orbit test, `V = DF`). -/
def commOp (hd : 2 ≤ d) (lam : ℝ) (κ : Vec d → ℝ) (V : FieldPair d → Vec d) (w : FieldPair d) :
    ℝ :=
  ∑ j, ∫ x, commKernel hd lam κ w j x * V (translate x w) j

/-- Products of a smooth compactly supported kernel (or its derivative) with bounded measurable
functions are integrable. -/
theorem integrable_kernel_mul_bdd {κ : Vec d → ℝ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    {g : Vec d → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Integrable (fun x => κ x * g x) :=
  (hκ.integrable_of_hasCompactSupport hκc).mul_bdd hg.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- `D_j F` along the orbit of `w`. -/
def orbitDeriv (F : FieldPair d → ℝ) (w : FieldPair d) (j : Fin d) (x : Vec d) : ℝ :=
  fderiv ℝ (orbit F w) x (unitVector j)

/-- `D_k D_j F` along the orbit of `w`. -/
def orbitDeriv2 (F : FieldPair d → ℝ) (w : FieldPair d) (j k : Fin d) (x : Vec d) : ℝ :=
  fderiv ℝ (orbitDeriv F w j) x (unitVector k)

/-- `∂_k a_{jk}` along the orbit of `w`. -/
def coeffDeriv (w : FieldPair d) (j k : Fin d) (x : Vec d) : ℝ :=
  fderiv ℝ (fun y => w.1 y j k) x (unitVector k)

theorem horizontalDerivative_translate_eq_orbitDeriv (F : FieldPair d → ℝ) (w : FieldPair d)
    (j : Fin d) (x : Vec d) : horizontalDerivative j F (translate x w) = orbitDeriv F w j x :=
  horizontalDerivative_translate j F w x

theorem horizontalDerivative2_translate_eq_orbitDeriv2 (F : FieldPair d → ℝ) (w : FieldPair d)
    (j k : Fin d) (x : Vec d) :
    horizontalDerivative k (horizontalDerivative j F) (translate x w) = orbitDeriv2 F w j k x := by
  rw [horizontalDerivative_translate]
  have : orbit (horizontalDerivative j F) w = orbitDeriv F w j :=
    funext fun y => horizontalDerivative_translate j F w y
  rw [this]
  rfl

/-- **Lemma A**: the generator of a smoothed test, by `D (S_κ F) = S_κ (D F)`. -/
theorem envGenerator_horizontalMollify (hd : 2 ≤ d) (lam : ℝ) {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (w : FieldPair d) :
    envGenerator hd lam (horizontalMollify κ F) w =
      (1 / 2 : ℝ) * ∑ k, ∑ j, (coeffDeriv w j k 0 * (∫ x, κ x * orbitDeriv F w j x) +
          w.1 0 j k * (∫ x, κ x * orbitDeriv2 F w j k x)) +
        lam * ∑ j, w.1 0 j (firstCoordinateIndex hd) * (∫ x, κ x * orbitDeriv F w j x) := by
  have h1 : ∀ j, horizontalDerivative j (horizontalMollify κ F) =
      horizontalMollify κ (horizontalDerivative j F) := fun j =>
    funext (horizontalDerivative_horizontalMollify_eq hκ hκc hF j)
  have h2 : ∀ j k, horizontalDerivative k (horizontalMollify κ (horizontalDerivative j F)) =
      horizontalMollify κ (horizontalDerivative k (horizontalDerivative j F)) := fun j k =>
    funext (horizontalDerivative_horizontalMollify_eq hκ hκc (hF.horizontalDerivative j) k)
  have h3 : ∀ j, horizontalMollify κ (horizontalDerivative j F) w =
      ∫ x, κ x * orbitDeriv F w j x := fun j => by
    unfold horizontalMollify
    simp only [horizontalDerivative_translate_eq_orbitDeriv]
  have h4 : ∀ j k, horizontalMollify κ (horizontalDerivative k (horizontalDerivative j F)) w =
      ∫ x, κ x * orbitDeriv2 F w j k x := fun j k => by
    unfold horizontalMollify
    simp only [horizontalDerivative2_translate_eq_orbitDeriv2]
  unfold envGenerator
  simp only [h1, h2, h3, h4]
  rfl

theorem orbitDeriv_eq_orbit (F : FieldPair d → ℝ) (w : FieldPair d) (j : Fin d) :
    orbitDeriv F w j = orbit (horizontalDerivative j F) w :=
  funext fun y => (horizontalDerivative_translate j F w y).symm

theorem orbitDeriv2_eq (F : FieldPair d → ℝ) (w : FieldPair d) (j k : Fin d) :
    orbitDeriv2 F w j k = orbitDeriv (horizontalDerivative j F) w k := by
  funext x
  unfold orbitDeriv2
  rw [orbitDeriv_eq_orbit]
  rfl

theorem continuous_orbitDeriv {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) (w : FieldPair d)
    (j : Fin d) : Continuous (orbitDeriv F w j) := by
  rw [orbitDeriv_eq_orbit]
  exact ((hF.horizontalDerivative j).2.1 w).continuous

theorem continuous_orbitDeriv2 {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) (w : FieldPair d)
    (j k : Fin d) : Continuous (orbitDeriv2 F w j k) := by
  rw [orbitDeriv2_eq]
  exact continuous_orbitDeriv (hF.horizontalDerivative j) w k

theorem measurable_coeffDeriv (w : FieldPair d) (j k : Fin d) : Measurable (coeffDeriv w j k) :=
  measurable_fderiv_apply_const ℝ _ _

theorem abs_coeffDeriv_le {w : FieldPair d} {j k : Fin d} {L : ℝ≥0}
    (hL : LipschitzWith L fun y => w.1 y j k) (x : Vec d) :
    |coeffDeriv w j k x| ≤ L * ‖unitVector (d := d) k‖ := by
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))

/-- Splitting the integral of `c₁ ∑ₖ ∑ⱼ (Aₖⱼ + Bₖⱼ) + c₂ ∑ⱼ Cⱼ`. -/
theorem integral_lincomb_sums (A B : Fin d → Fin d → Vec d → ℝ) (C : Fin d → Vec d → ℝ)
    (hA : ∀ k j, Integrable (A k j)) (hB : ∀ k j, Integrable (B k j)) (hC : ∀ j, Integrable (C j))
    (c₁ c₂ : ℝ) :
    ∫ x, (c₁ * ∑ k, ∑ j, (A k j x + B k j x) + c₂ * ∑ j, C j x) =
      c₁ * ∑ k, ∑ j, ((∫ x, A k j x) + ∫ x, B k j x) + c₂ * ∑ j, ∫ x, C j x := by
  have hAB : ∀ k j, Integrable (fun x => A k j x + B k j x) := fun k j => (hA k j).add (hB k j)
  have hS1 : Integrable (fun x => ∑ k, ∑ j, (A k j x + B k j x)) :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ => hAB k j
  have hS2 : Integrable (fun x => ∑ j, C j x) := integrable_finset_sum _ fun j _ => hC j
  rw [integral_add (hS1.const_mul c₁) (hS2.const_mul c₂), integral_const_mul, integral_const_mul,
    integral_finset_sum _ fun j _ => hC j]
  congr 2
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ => hAB k j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ fun j _ => hAB k j]
  exact Finset.sum_congr rfl fun j _ => integral_add (hA k j) (hB k j)

/-- **Lemma B**: the smoothing of the generator, expanded along the orbit. -/
theorem horizontalMollify_envGenerator (hd : 2 ≤ d) (lam : ℝ) {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) {w : FieldPair d} {K : ℝ} {L : ℝ≥0}
    (hwB : ∀ x j k, |w.1 x j k| ≤ K) (hwL : ∀ j k, LipschitzWith L fun y => w.1 y j k) :
    horizontalMollify κ (envGenerator hd lam F) w =
      (1 / 2 : ℝ) * ∑ k, ∑ j, ((∫ x, κ x * (coeffDeriv w j k x * orbitDeriv F w j x)) +
          ∫ x, κ x * (w.1 x j k * orbitDeriv2 F w j k x)) +
        lam * ∑ j, ∫ x, κ x * (w.1 x j (firstCoordinateIndex hd) * orbitDeriv F w j x) := by
  obtain ⟨M0, M1, M2, -, -, -, hb1, hb2⟩ := hF.exists_bounds
  have hentry : ∀ j k, Continuous fun x : Vec d => w.1 x j k := fun j k =>
    (continuous_apply k).comp ((continuous_apply j).comp w.1.continuous)
  have hA : ∀ k j, Integrable fun x => κ x * (coeffDeriv w j k x * orbitDeriv F w j x) :=
    fun k j => integrable_kernel_mul_bdd hκ.continuous hκc
      ((measurable_coeffDeriv w j k).mul (continuous_orbitDeriv hF w j).measurable)
      (C := L * ‖unitVector (d := d) k‖ * M1) fun x => by
        rw [abs_mul]
        exact mul_le_mul (abs_coeffDeriv_le (hwL j k) x) (hb1 w x j) (abs_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
  have hB : ∀ k j, Integrable fun x => κ x * (w.1 x j k * orbitDeriv2 F w j k x) :=
    fun k j => integrable_kernel_mul_bdd hκ.continuous hκc
      ((hentry j k).measurable.mul (continuous_orbitDeriv2 hF w j k).measurable)
      (C := K * M2) fun x => by
        rw [abs_mul]
        exact mul_le_mul (hwB x j k) (hb2 w x j k) (abs_nonneg _) ((abs_nonneg _).trans (hwB x j k))
  have hC : ∀ j, Integrable fun x =>
      κ x * (w.1 x j (firstCoordinateIndex hd) * orbitDeriv F w j x) :=
    fun j => integrable_kernel_mul_bdd hκ.continuous hκc
      ((hentry j _).measurable.mul (continuous_orbitDeriv hF w j).measurable)
      (C := K * M1) fun x => by
        rw [abs_mul]
        exact mul_le_mul (hwB x j _) (hb1 w x j) (abs_nonneg _) ((abs_nonneg _).trans (hwB x j j))
  have e : (fun x => κ x * envGenerator hd lam F (translate x w)) = fun x =>
      (1 / 2 : ℝ) * ∑ k, ∑ j, (κ x * (coeffDeriv w j k x * orbitDeriv F w j x) +
          κ x * (w.1 x j k * orbitDeriv2 F w j k x)) +
        lam * ∑ j, κ x * (w.1 x j (firstCoordinateIndex hd) * orbitDeriv F w j x) := by
    funext x
    rw [envGenerator_translate]
    unfold coeffDeriv orbitDeriv2 orbitDeriv
    simp only [mul_add, Finset.mul_sum]
    ring
  unfold horizontalMollify
  rw [e, integral_lincomb_sums _ _ _ hA hB hC]

theorem lipschitzWith_orbitDeriv {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) {M2 : ℝ}
    (hb2 : ∀ w x j k,
      |fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k)| ≤ M2)
    (w : FieldPair d) (j : Fin d) :
    LipschitzWith (d * M2).toNNReal (orbitDeriv F w j) ∧ Differentiable ℝ (orbitDeriv F w j) := by
  have hd : Differentiable ℝ (orbitDeriv F w j) := by
    rw [orbitDeriv_eq_orbit]
    exact ((hF.horizontalDerivative j).2.1 w).differentiable (by simp)
  exact ⟨lipschitzWith_of_coordinateDerivative_le hd fun x k => hb2 w x j k, hd⟩

/-- **Lemma C**: the `(j, k)` term of the commutator. -/
theorem commutator_term_jk {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) {F : FieldPair d → ℝ} (hF : IsHorizontalTest F)
    {w : FieldPair d} {K : ℝ} {L : ℝ≥0} (hwB : ∀ x j k, |w.1 x j k| ≤ K)
    (hwL : ∀ j k, LipschitzWith L fun y => w.1 y j k) (j k : Fin d) :
    coeffDeriv w j k 0 * (∫ x, κ x * orbitDeriv F w j x) +
        w.1 0 j k * (∫ x, κ x * orbitDeriv2 F w j k x) -
      ((∫ x, κ x * (coeffDeriv w j k x * orbitDeriv F w j x)) +
        ∫ x, κ x * (w.1 x j k * orbitDeriv2 F w j k x)) =
      ∫ x, (κ x * coeffDeriv w j k 0 - coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) *
        orbitDeriv F w j x := by
  obtain ⟨M0, M1, M2, hM1, hM2, -, hb1, hb2⟩ := hF.exists_bounds
  obtain ⟨hLψ, hψd⟩ := lipschitzWith_orbitDeriv hF hb2 w j
  have hentry : Continuous fun x : Vec d => w.1 x j k :=
    (continuous_apply k).comp ((continuous_apply j).comp w.1.continuous)
  have hψc := continuous_orbitDeriv hF w j
  have hψ2c := continuous_orbitDeriv2 hF w j k
  have hκ1 : Continuous fun x => coordinateDerivative k κ x :=
    (hκ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hκ1c : HasCompactSupport fun x => coordinateDerivative k κ x :=
    hκc.fderiv_apply (𝕜 := ℝ) (unitVector k)
  have hcd : ∀ x, |coeffDeriv w j k x| ≤ L * ‖unitVector (d := d) k‖ :=
    abs_coeffDeriv_le (hwL j k)
  have hLe : 0 ≤ (L : ℝ) * ‖unitVector (d := d) k‖ :=
    mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hwB 0 j k)
  have hI1 : Integrable fun x => κ x * ((coeffDeriv w j k 0 - coeffDeriv w j k x) *
      orbitDeriv F w j x) :=
    integrable_kernel_mul_bdd hκ.continuous hκc
      ((measurable_const.sub (measurable_coeffDeriv w j k)).mul hψc.measurable)
      (C := (L * ‖unitVector (d := d) k‖ + L * ‖unitVector (d := d) k‖) * M1) fun x => by
        rw [abs_mul]
        exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hcd 0) (hcd x))) (hb1 w x j)
          (abs_nonneg _) (by positivity)
  have hI2 : Integrable fun x => κ x * ((w.1 0 j k - w.1 x j k) * orbitDeriv2 F w j k x) :=
    integrable_kernel_mul_bdd hκ.continuous hκc
      ((measurable_const.sub hentry.measurable).mul hψ2c.measurable)
      (C := (K + K) * M2) fun x => by
        rw [abs_mul]
        exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hwB 0 j k) (hwB x j k))) (hb2 w x j k)
          (abs_nonneg _) (by positivity)
  have hIa : Integrable fun x => κ x * orbitDeriv F w j x :=
    integrable_kernel_mul_bdd hκ.continuous hκc hψc.measurable (C := M1) fun x => hb1 w x j
  have hIb : Integrable fun x => κ x * orbitDeriv2 F w j k x :=
    integrable_kernel_mul_bdd hκ.continuous hκc hψ2c.measurable (C := M2) fun x => hb2 w x j k
  have hIc : Integrable fun x => κ x * (coeffDeriv w j k x * orbitDeriv F w j x) :=
    integrable_kernel_mul_bdd hκ.continuous hκc
      ((measurable_coeffDeriv w j k).mul hψc.measurable)
      (C := L * ‖unitVector (d := d) k‖ * M1) fun x => by
        rw [abs_mul]
        exact mul_le_mul (hcd x) (hb1 w x j) (abs_nonneg _) hLe
  have hId : Integrable fun x => κ x * (w.1 x j k * orbitDeriv2 F w j k x) :=
    integrable_kernel_mul_bdd hκ.continuous hκc (hentry.measurable.mul hψ2c.measurable)
      (C := K * M2) fun x => by
        rw [abs_mul]
        exact mul_le_mul (hwB x j k) (hb2 w x j k) (abs_nonneg _) hK0
  have hI3 : Integrable fun x => (-(coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) +
      κ x * coeffDeriv w j k x) * orbitDeriv F w j x := by
    have h1 : Integrable fun x => coordinateDerivative k κ x *
        ((w.1 0 j k - w.1 x j k) * orbitDeriv F w j x) :=
      integrable_kernel_mul_bdd hκ1 hκ1c ((measurable_const.sub hentry.measurable).mul hψc.measurable)
        (C := (K + K) * M1) fun x => by
          rw [abs_mul]
          exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hwB 0 j k) (hwB x j k))) (hb1 w x j)
            (abs_nonneg _) (by positivity)
    refine (h1.neg.add hIc).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  have e1 : coeffDeriv w j k 0 * (∫ x, κ x * orbitDeriv F w j x) -
      ∫ x, κ x * (coeffDeriv w j k x * orbitDeriv F w j x) =
      ∫ x, κ x * ((coeffDeriv w j k 0 - coeffDeriv w j k x) * orbitDeriv F w j x) := by
    rw [← integral_const_mul, ← integral_sub (hIa.const_mul _) hIc]
    congr 1
    funext x
    ring
  have e2 : w.1 0 j k * (∫ x, κ x * orbitDeriv2 F w j k x) -
      ∫ x, κ x * (w.1 x j k * orbitDeriv2 F w j k x) =
      ∫ x, κ x * ((w.1 0 j k - w.1 x j k) * orbitDeriv2 F w j k x) := by
    rw [← integral_const_mul, ← integral_sub (hIb.const_mul _) hId]
    congr 1
    funext x
    ring
  have e3 : ∫ x, κ x * ((w.1 0 j k - w.1 x j k) * orbitDeriv2 F w j k x) =
      ∫ x, (-(coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) +
        κ x * coeffDeriv w j k x) * orbitDeriv F w j x := by
    have h := integral_kernel_coeff_deriv hκ hκc (hwL j k) (fun x => hwB x j k) hLψ hψd k
    have e : (fun x => κ x * ((w.1 0 j k - w.1 x j k) * orbitDeriv2 F w j k x)) =
        fun x => κ x * (w.1 0 j k - w.1 x j k) * fderiv ℝ (orbitDeriv F w j) x (unitVector k) := by
      funext x
      unfold orbitDeriv2
      ring
    rw [e]
    exact h
  have e4 : (∫ x, κ x * ((coeffDeriv w j k 0 - coeffDeriv w j k x) * orbitDeriv F w j x)) +
      (∫ x, (-(coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) +
        κ x * coeffDeriv w j k x) * orbitDeriv F w j x) =
      ∫ x, (κ x * coeffDeriv w j k 0 - coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) *
        orbitDeriv F w j x := by
    rw [← integral_add hI1 hI3]
    congr 1
    funext x
    ring
  calc coeffDeriv w j k 0 * (∫ x, κ x * orbitDeriv F w j x) +
        w.1 0 j k * (∫ x, κ x * orbitDeriv2 F w j k x) -
      ((∫ x, κ x * (coeffDeriv w j k x * orbitDeriv F w j x)) +
        ∫ x, κ x * (w.1 x j k * orbitDeriv2 F w j k x))
      = (coeffDeriv w j k 0 * (∫ x, κ x * orbitDeriv F w j x) -
          ∫ x, κ x * (coeffDeriv w j k x * orbitDeriv F w j x)) +
        (w.1 0 j k * (∫ x, κ x * orbitDeriv2 F w j k x) -
          ∫ x, κ x * (w.1 x j k * orbitDeriv2 F w j k x)) := by ring
    _ = _ := by rw [e1, e2, e3, e4]

/-- **Lemma D**: the drift term of the commutator. -/
theorem commutator_term_j {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) {F : FieldPair d → ℝ} (hF : IsHorizontalTest F)
    {w : FieldPair d} {K : ℝ} (hwB : ∀ x j k, |w.1 x j k| ≤ K) (j i : Fin d) :
    w.1 0 j i * (∫ x, κ x * orbitDeriv F w j x) - ∫ x, κ x * (w.1 x j i * orbitDeriv F w j x) =
      ∫ x, κ x * (w.1 0 j i - w.1 x j i) * orbitDeriv F w j x := by
  obtain ⟨M0, M1, M2, -, -, -, hb1, -⟩ := hF.exists_bounds
  have hentry : Continuous fun x : Vec d => w.1 x j i :=
    (continuous_apply i).comp ((continuous_apply j).comp w.1.continuous)
  have hψc := continuous_orbitDeriv hF w j
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hwB 0 j i)
  have hIa : Integrable fun x => κ x * orbitDeriv F w j x :=
    integrable_kernel_mul_bdd hκ.continuous hκc hψc.measurable (C := M1) fun x => hb1 w x j
  have hIc : Integrable fun x => κ x * (w.1 x j i * orbitDeriv F w j x) :=
    integrable_kernel_mul_bdd hκ.continuous hκc (hentry.measurable.mul hψc.measurable)
      (C := K * M1) fun x => by
        rw [abs_mul]
        exact mul_le_mul (hwB x j i) (hb1 w x j) (abs_nonneg _) hK0
  rw [← integral_const_mul, ← integral_sub (hIa.const_mul _) hIc]
  congr 1
  funext x
  ring

/-- **Lemma E**: the commutator operator on `DF`, expanded. -/
theorem commOp_horizontalDerivative (hd : 2 ≤ d) (lam : ℝ) {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) {w : FieldPair d} {K : ℝ} (hwB : ∀ x j k, |w.1 x j k| ≤ K) :
    commOp hd lam κ (fun w' j => horizontalDerivative j F w') w =
      ∑ j, ((1 / 2 : ℝ) * ∑ k, (∫ x, (κ x * coeffDeriv w j k 0 -
          coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) * orbitDeriv F w j x) +
        lam * ∫ x, κ x * (w.1 0 j (firstCoordinateIndex hd) - w.1 x j (firstCoordinateIndex hd)) *
          orbitDeriv F w j x) := by
  obtain ⟨M0, M1, M2, -, -, -, hb1, -⟩ := hF.exists_bounds
  unfold commOp
  refine Finset.sum_congr rfl fun j _ => ?_
  have hψc := continuous_orbitDeriv hF w j
  have hκ1 : ∀ k, Continuous fun x => coordinateDerivative k κ x := fun k =>
    (hκ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hκ1c : ∀ k, HasCompactSupport fun x => coordinateDerivative k κ x := fun k =>
    hκc.fderiv_apply (𝕜 := ℝ) (unitVector k)
  have hentry : ∀ i, Continuous fun x : Vec d => w.1 x j i := fun i =>
    (continuous_apply i).comp ((continuous_apply j).comp w.1.continuous)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hwB 0 j j)
  have hT : ∀ k, Integrable fun x => (κ x * coeffDeriv w j k 0 -
      coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) * orbitDeriv F w j x := by
    intro k
    have h1 : Integrable fun x => κ x * (coeffDeriv w j k 0 * orbitDeriv F w j x) :=
      integrable_kernel_mul_bdd hκ.continuous hκc (measurable_const.mul hψc.measurable)
        (C := |coeffDeriv w j k 0| * M1) fun x => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hb1 w x j) (abs_nonneg _)
    have h2 : Integrable fun x => coordinateDerivative k κ x *
        ((w.1 0 j k - w.1 x j k) * orbitDeriv F w j x) :=
      integrable_kernel_mul_bdd (hκ1 k) (hκ1c k)
        ((measurable_const.sub (hentry k).measurable).mul hψc.measurable)
        (C := (K + K) * M1) fun x => by
          rw [abs_mul]
          exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hwB 0 j k) (hwB x j k))) (hb1 w x j)
            (abs_nonneg _) (by positivity)
    refine (h1.sub h2).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hU : Integrable fun x => κ x * (w.1 0 j (firstCoordinateIndex hd) -
      w.1 x j (firstCoordinateIndex hd)) * orbitDeriv F w j x := by
    have h := integrable_kernel_mul_bdd hκ.continuous hκc
      (((measurable_const (a := w.1 0 j (firstCoordinateIndex hd))).fun_sub
        (hentry (firstCoordinateIndex hd)).measurable).fun_mul hψc.measurable)
      (C := (K + K) * M1) fun x => by
        rw [abs_mul]
        exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hwB 0 j (firstCoordinateIndex hd))
          (hwB x j (firstCoordinateIndex hd)))) (hb1 w x j) (abs_nonneg _) (by positivity)
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only
    ring
  have e : (fun x => commKernel hd lam κ w j x * horizontalDerivative j F (translate x w)) =
      fun x => (1 / 2 : ℝ) * ∑ k, (κ x * coeffDeriv w j k 0 -
          coordinateDerivative k κ x * (w.1 0 j k - w.1 x j k)) * orbitDeriv F w j x +
        lam * (κ x * (w.1 0 j (firstCoordinateIndex hd) - w.1 x j (firstCoordinateIndex hd)) *
          orbitDeriv F w j x) := by
    funext x
    rw [horizontalDerivative_translate_eq_orbitDeriv]
    unfold commKernel coeffDeriv
    rw [add_mul, mul_assoc (1 / 2 : ℝ), Finset.sum_mul]
    ring
  rw [e, integral_add ((integrable_finset_sum _ fun k _ => hT k).const_mul _) (hU.const_mul _),
    integral_const_mul, integral_const_mul, integral_finset_sum _ fun k _ => hT k]

/-- **The commutator identity.** For a regular orbit (bounded Lipschitz coefficient entries),
`L (S_κ F) - S_κ (L F) = commOp κ (DF)`: the commutator involves no second derivative of `F`. -/
theorem envGenerator_horizontalMollify_sub (hd : 2 ≤ d) (lam : ℝ) {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) {w : FieldPair d} {K : ℝ} {L : ℝ≥0}
    (hwB : ∀ x j k, |w.1 x j k| ≤ K) (hwL : ∀ j k, LipschitzWith L fun y => w.1 y j k) :
    envGenerator hd lam (horizontalMollify κ F) w -
        horizontalMollify κ (envGenerator hd lam F) w =
      commOp hd lam κ (fun w' j => horizontalDerivative j F w') w := by
  rw [envGenerator_horizontalMollify hd lam hκ hκc hF w,
    horizontalMollify_envGenerator hd lam hκ hκc hF hwB hwL,
    commOp_horizontalDerivative hd lam hκ hκc hF hwB]
  have hC := fun j k => commutator_term_jk hκ hκc hF hwB hwL j k
  have hD := fun j => commutator_term_j hκ hκc hF hwB j (firstCoordinateIndex hd)
  have h1 : (1 / 2 : ℝ) * ∑ k, ∑ j, (coeffDeriv w j k 0 * (∫ x, κ x * orbitDeriv F w j x) +
          w.1 0 j k * (∫ x, κ x * orbitDeriv2 F w j k x)) +
        lam * ∑ j, w.1 0 j (firstCoordinateIndex hd) * (∫ x, κ x * orbitDeriv F w j x) -
      ((1 / 2 : ℝ) * ∑ k, ∑ j, ((∫ x, κ x * (coeffDeriv w j k x * orbitDeriv F w j x)) +
          ∫ x, κ x * (w.1 x j k * orbitDeriv2 F w j k x)) +
        lam * ∑ j, ∫ x, κ x * (w.1 x j (firstCoordinateIndex hd) * orbitDeriv F w j x)) =
      (1 / 2 : ℝ) * ∑ k, ∑ j, (coeffDeriv w j k 0 * (∫ x, κ x * orbitDeriv F w j x) +
          w.1 0 j k * (∫ x, κ x * orbitDeriv2 F w j k x) -
        ((∫ x, κ x * (coeffDeriv w j k x * orbitDeriv F w j x)) +
          ∫ x, κ x * (w.1 x j k * orbitDeriv2 F w j k x))) +
      lam * ∑ j, (w.1 0 j (firstCoordinateIndex hd) * (∫ x, κ x * orbitDeriv F w j x) -
        ∫ x, κ x * (w.1 x j (firstCoordinateIndex hd) * orbitDeriv F w j x)) := by
    simp only [Finset.sum_sub_distrib]
    ring
  rw [h1]
  simp only [hC, hD]
  rw [Finset.sum_comm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## Bounds for the commutator -/

theorem coordinateDerivative_unitMassScaledMollifier {δ : ℝ} (k : Fin d) (x : Vec d) :
    coordinateDerivative k (Calculus.unitMassScaledMollifier d δ) x =
      (δ ^ d)⁻¹ * δ⁻¹ * coordinateDerivative k (mollifier d) (δ⁻¹ • x) := by
  have hm : DifferentiableAt ℝ (mollifier d) (δ⁻¹ • x) :=
    ((contDiff_mollifier d).differentiable (by simp)) _
  have hs : HasFDerivAt (fun y : Vec d => δ⁻¹ • y) (δ⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).const_smul δ⁻¹
  have hc := (hm.hasFDerivAt.comp x hs).const_mul (δ ^ d)⁻¹
  unfold coordinateDerivative Calculus.unitMassScaledMollifier
  rw [show (fun x : Vec d => (δ ^ d)⁻¹ * mollifier d (δ⁻¹ • x)) =
    fun x => (δ ^ d)⁻¹ * (mollifier d ∘ fun y => δ⁻¹ • y) x from rfl, hc.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_smul]
  ring

theorem integral_abs_coordinateDerivative_unitMassScaledMollifier {δ : ℝ} (hδ : 0 < δ)
    (k : Fin d) :
    ∫ x, |coordinateDerivative k (Calculus.unitMassScaledMollifier d δ) x| =
      δ⁻¹ * ∫ u, |coordinateDerivative k (mollifier d) u| := by
  have hpos : 0 < (δ ^ d)⁻¹ * δ⁻¹ := by positivity
  simp only [coordinateDerivative_unitMassScaledMollifier, abs_mul, abs_of_pos hpos]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
    (fun u => |coordinateDerivative k (mollifier d) u|) hδ.le, Module.finrank_fin_fun,
    smul_eq_mul]
  field_simp

theorem coordinateDerivative_unitMassScaledMollifier_eq_zero {δ : ℝ} (hδ : 0 < δ) (k : Fin d)
    {x : Vec d} (hx : δ < euclideanNorm x) :
    coordinateDerivative k (Calculus.unitMassScaledMollifier d δ) x = 0 := by
  have hsub : tsupport (Calculus.unitMassScaledMollifier d δ) ⊆
      {z : Vec d | euclideanNorm z ≤ δ} := by
    refine closure_minimal (fun z hz => ?_)
      (isClosed_le continuous_euclideanNorm' continuous_const)
    exact (euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hδ hz).le
  have hnot : x ∉ tsupport (Calculus.unitMassScaledMollifier d δ) := fun hmem => by
    have := hsub hmem
    simp only [Set.mem_setOf_eq] at this
    linarith
  show fderiv ℝ (Calculus.unitMassScaledMollifier d δ) x (unitVector k) = 0
  rw [fderiv_of_notMem_tsupport ℝ hnot]
  simp

theorem norm_le_euclideanNorm'' (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
  have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_apply_le_euclideanNorm x i

/-- A deterministic bound for the commutator kernel of the rescaled mollifier. -/
def commBound (d : ℕ) (lam δ : ℝ) (L : ℝ≥0) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∑ k : Fin d, (Calculus.unitMassScaledMollifier d δ x * (L * ‖unitVector (d := d) k‖) +
      |coordinateDerivative k (Calculus.unitMassScaledMollifier d δ) x| * (L * ‖x‖)) +
    |lam| * (Calculus.unitMassScaledMollifier d δ x * (L * ‖x‖))

theorem abs_commKernel_le (hd : 2 ≤ d) (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) {w : FieldPair d}
    {L : ℝ≥0} (hwL : ∀ j k, LipschitzWith L fun y => w.1 y j k) (j : Fin d) (x : Vec d) :
    |commKernel hd lam (Calculus.unitMassScaledMollifier d δ) w j x| ≤ commBound d lam δ L x := by
  have hκ0 := unitMassScaledMollifier_nonneg' hδ x
  have hinc : ∀ k, |w.1 0 j k - w.1 x j k| ≤ L * ‖x‖ := fun k => by
    have h := (hwL j k).dist_le_mul 0 x
    rwa [Real.dist_eq, dist_eq_norm, zero_sub, norm_neg] at h
  unfold commKernel commBound
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k _ => ?_)) (by norm_num)
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hκ0]
      exact mul_le_mul_of_nonneg_left (abs_coeffDeriv_le (hwL j k) 0) hκ0
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hinc k) (abs_nonneg _)
  · rw [abs_mul, abs_mul, abs_of_nonneg hκ0]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinc _) hκ0) (abs_nonneg _)

theorem continuous_coordinateDerivative_unitMassScaledMollifier (δ : ℝ) (k : Fin d) :
    Continuous (coordinateDerivative k (Calculus.unitMassScaledMollifier d δ)) :=
  ((contDiff_unitMassScaledMollifier δ).continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_coordinateDerivative_unitMassScaledMollifier {δ : ℝ} (hδ : 0 < δ)
    (k : Fin d) :
    HasCompactSupport (coordinateDerivative k (Calculus.unitMassScaledMollifier d δ)) :=
  (hasCompactSupport_unitMassScaledMollifier hδ).fderiv_apply (𝕜 := ℝ) (unitVector k)

theorem continuous_commBound (d : ℕ) (lam δ : ℝ) (L : ℝ≥0) : Continuous (commBound d lam δ L) := by
  unfold commBound
  have hκ := (contDiff_unitMassScaledMollifier (d := d) δ).continuous
  have hk := fun k : Fin d => continuous_coordinateDerivative_unitMassScaledMollifier (d := d) δ k
  exact (continuous_const.mul (continuous_finset_sum _ fun k _ => (hκ.mul continuous_const).add
    ((hk k).abs.mul (continuous_const.mul continuous_norm)))).add
    (continuous_const.mul (hκ.mul (continuous_const.mul continuous_norm)))

theorem integrable_commBound (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) (L : ℝ≥0) :
    Integrable (commBound d lam δ L) := by
  refine (continuous_commBound d lam δ L).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) δ) fun x hx => ?_
  have hx' : δ < euclideanNorm x := by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact lt_of_lt_of_le hx (norm_le_euclideanNorm'' x)
  have hκ : Calculus.unitMassScaledMollifier d δ x = 0 := by
    by_contra h
    exact absurd (euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hδ h) (not_lt.mpr hx'.le)
  unfold commBound
  simp [hκ, coordinateDerivative_unitMassScaledMollifier_eq_zero hδ _ hx']

/-- The `L¹` norm of the commutator bound is uniform in the scale `δ ≤ 1`. -/
def commConst (d : ℕ) (lam : ℝ) (L : ℝ≥0) : ℝ :=
  (1 / 2 : ℝ) * ∑ k : Fin d, (L * ‖unitVector (d := d) k‖ +
      L * ∫ u, |coordinateDerivative k (mollifier d) u|) + |lam| * L

theorem integral_commBound_le (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (L : ℝ≥0) :
    ∫ x, commBound d lam δ L x ≤ commConst d lam L := by
  set κ := Calculus.unitMassScaledMollifier d δ with hκdef
  have hκc := (contDiff_unitMassScaledMollifier (d := d) δ).continuous
  have hκi : Integrable κ := hκc.integrable_of_hasCompactSupport
    (hasCompactSupport_unitMassScaledMollifier hδ)
  have hki : ∀ k, Integrable fun x => |coordinateDerivative k κ x| := fun k =>
    ((continuous_coordinateDerivative_unitMassScaledMollifier δ k).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative_unitMassScaledMollifier hδ k)).abs
  have hκ0 := fun x => unitMassScaledMollifier_nonneg' (d := d) hδ x
  have hκx : ∀ x, κ x * ‖x‖ ≤ κ x * δ := fun x => by
    by_cases h : κ x = 0
    · rw [h, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left ((norm_le_euclideanNorm'' x).trans
        (euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hδ h).le) (hκ0 x)
  have hkx : ∀ k x, |coordinateDerivative k κ x| * ‖x‖ ≤ |coordinateDerivative k κ x| * δ :=
    fun k x => by
      by_cases h : δ < euclideanNorm x
      · rw [coordinateDerivative_unitMassScaledMollifier_eq_zero hδ k h, abs_zero, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left ((norm_le_euclideanNorm'' x).trans (not_lt.mp h))
          (abs_nonneg _)
  set g : Vec d → ℝ := fun x => (1 / 2 : ℝ) * ∑ k : Fin d, (κ x * (L * ‖unitVector (d := d) k‖) +
      |coordinateDerivative k κ x| * (L * δ)) + |lam| * (κ x * (L * δ)) with hgdef
  have hle : ∀ x, commBound d lam δ L x ≤ g x := fun x => by
    unfold commBound
    refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => add_le_add le_rfl ?_)
      (by norm_num)) (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    · calc |coordinateDerivative k κ x| * (L * ‖x‖) = L * (|coordinateDerivative k κ x| * ‖x‖) := by
            ring
        _ ≤ L * (|coordinateDerivative k κ x| * δ) :=
            mul_le_mul_of_nonneg_left (hkx k x) (NNReal.coe_nonneg _)
        _ = |coordinateDerivative k κ x| * (L * δ) := by ring
    · calc κ x * (L * ‖x‖) = L * (κ x * ‖x‖) := by ring
        _ ≤ L * (κ x * δ) := mul_le_mul_of_nonneg_left (hκx x) (NNReal.coe_nonneg _)
        _ = κ x * (L * δ) := by ring
  have hT : ∀ k : Fin d, Integrable fun x => κ x * (L * ‖unitVector (d := d) k‖) +
      |coordinateDerivative k κ x| * (L * δ) := fun k =>
    (hκi.mul_const _).add ((hki k).mul_const _)
  have hS : Integrable fun x => ∑ k : Fin d, (κ x * (L * ‖unitVector (d := d) k‖) +
      |coordinateDerivative k κ x| * (L * δ)) := integrable_finset_sum _ fun k _ => hT k
  have hU : Integrable fun x => |lam| * (κ x * (L * δ)) := (hκi.mul_const _).const_mul _
  have hgi : Integrable g := (hS.const_mul _).add hU
  have hint : ∫ x, g x = (1 / 2 : ℝ) * ∑ k : Fin d, (L * ‖unitVector (d := d) k‖ +
      L * δ * (δ⁻¹ * ∫ u, |coordinateDerivative k (mollifier d) u|)) + |lam| * (L * δ) := by
    show ∫ x, ((1 / 2 : ℝ) * ∑ k : Fin d, (κ x * (L * ‖unitVector (d := d) k‖) +
      |coordinateDerivative k κ x| * (L * δ)) + |lam| * (κ x * (L * δ))) = _
    rw [integral_add (hS.const_mul _) hU, integral_const_mul, integral_const_mul,
      integral_finset_sum _ fun k _ => hT k]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_add (hκi.mul_const _) ((hki k).mul_const _), integral_mul_const,
        integral_mul_const, integral_unitMassScaledMollifier' hδ,
        integral_abs_coordinateDerivative_unitMassScaledMollifier hδ]
      ring
    · rw [integral_mul_const, integral_unitMassScaledMollifier' hδ]
      ring
  calc ∫ x, commBound d lam δ L x ≤ ∫ x, g x :=
        integral_mono (integrable_commBound lam hδ L) hgi hle
    _ = _ := hint
    _ ≤ commConst d lam L := by
        unfold commConst
        have hδne : δ ≠ 0 := hδ.ne'
        have e : ∀ k : Fin d, (L : ℝ) * δ * (δ⁻¹ * ∫ u, |coordinateDerivative k (mollifier d) u|) =
            L * ∫ u, |coordinateDerivative k (mollifier d) u| := fun k => by field_simp
        simp only [e]
        gcongr
        calc (L : ℝ) * δ ≤ L * 1 := mul_le_mul_of_nonneg_left hδ1 (NNReal.coe_nonneg _)
          _ = L := mul_one _

/-! ## `L²` estimates -/

theorem abs_integral_mul_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ a, f a * g a ∂μ| ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ) := by
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  have hfa : MemLp (fun a => |f a|) (ENNReal.ofReal 2) μ := by rw [h2]; exact hf.abs
  have hga : MemLp (fun a => |g a|) (ENNReal.ofReal 2) μ := by rw [h2]; exact hg.abs
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun a => abs_nonneg (f a)) (ae_of_all _ fun a => abs_nonneg (g a)) hfa hga
  have e : ∀ h : Ω → ℝ, (∫ a, |h a| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ a, h a ^ 2 ∂μ) := by
    intro h
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [Real.rpow_two, sq_abs]
  rw [e f, e g] at hH
  calc |∫ a, f a * g a ∂μ| ≤ ∫ a, |f a * g a| ∂μ := abs_integral_le_integral_abs
    _ = ∫ a, |f a| * |g a| ∂μ := integral_congr_ae (ae_of_all _ fun a => abs_mul _ _)
    _ ≤ _ := hH

theorem integral_sq_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (h : eLpNorm f 2 μ ≤ eLpNorm g 2 μ) :
    ∫ a, f a ^ 2 ∂μ ≤ ∫ a, g a ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top] at h
  have hf0 : 0 ≤ ∫ a, ‖f a‖ ^ (2 : ℝ≥0∞).toReal ∂μ := integral_nonneg fun a => by positivity
  have hg0 : 0 ≤ ∫ a, ‖g a‖ ^ (2 : ℝ≥0∞).toReal ∂μ := integral_nonneg fun a => by positivity
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have h' := (Real.rpow_le_rpow_iff (by positivity) (by positivity)
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal⁻¹)).mp h
  have e : ∀ u : Ω → ℝ, ∫ a, ‖u a‖ ^ (2 : ℝ≥0∞).toReal ∂μ = ∫ a, u a ^ 2 ∂μ := fun u =>
    integral_congr_ae (ae_of_all _ fun a => by
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])
  rwa [e f, e g] at h'

/-- The `L²` contraction of the smoothing by a nonnegative integrable kernel `k`. -/
theorem integral_sq_horizontalMollify_le {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {k : Vec d → ℝ} (hk0 : ∀ x, 0 ≤ k x) (hkm : Measurable k)
    (hki : Integrable k) {g : FieldPair d → ℝ} (hgm : Measurable g) (hg : MemLp g 2 Q) :
    MemLp (horizontalMollify k g) 2 Q ∧
      ∫ w, horizontalMollify k g w ^ 2 ∂Q ≤ (∫ x, k x) ^ 2 * ∫ w, g w ^ 2 ∂Q := by
  set m := ∫ x, k x with hmdef
  have hm0 : 0 ≤ m := integral_nonneg hk0
  have hSm : Measurable (horizontalMollify k g) := measurable_horizontalMollify k hkm hgm
  rcases hm0.lt_or_eq with hmpos | hm0'
  · set ζ : Vec d → ℝ := fun x => k x / m with hζdef
    have hζm : Measurable ζ := hkm.div_const m
    have hζ0 : ∀ x, 0 ≤ ζ x := fun x => div_nonneg (hk0 x) hm0
    have hζ1 : ∫ x, ζ x = 1 := by rw [hζdef, integral_div, ← hmdef, div_self hmpos.ne']
    have hS : horizontalMollify k g = fun w => m * horizontalMollify ζ g w := by
      funext w
      unfold horizontalMollify
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hζdef]
      field_simp
    haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
    have hle := Calculus.eLpNorm_horizontalMollify_le Q hQ 2 ENNReal.ofNat_ne_top hζm hζ0 hζ1 hgm
    have hSζm : Measurable (horizontalMollify ζ g) := measurable_horizontalMollify ζ hζm hgm
    have hSζ : MemLp (horizontalMollify ζ g) 2 Q :=
      hle.trans_lt hg.eLpNorm_lt_top
    refine ⟨by rw [hS]; exact hSζ.const_mul m, ?_⟩
    rw [hS]
    have h2 := integral_sq_le_of_eLpNorm_le hSζ hg hle
    calc ∫ w, (m * horizontalMollify ζ g w) ^ 2 ∂Q = m ^ 2 * ∫ w, horizontalMollify ζ g w ^ 2 ∂Q := by
          rw [← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun w => by ring)
      _ ≤ m ^ 2 * ∫ w, g w ^ 2 ∂Q := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  · have hk : k =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hk0 hki).mp hm0'.symm
    have hS : horizontalMollify k g = fun _ => 0 := by
      funext w
      unfold horizontalMollify
      exact integral_eq_zero_of_ae (hk.mono fun x hx => by simp [hx])
    rw [hS]
    refine ⟨MemLp.zero' (μ := Q), ?_⟩
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    exact mul_nonneg (sq_nonneg _) (integral_nonneg fun w => sq_nonneg _)

theorem commBound_nonneg (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) (L : ℝ≥0) (x : Vec d) :
    0 ≤ commBound d lam δ L x := by
  unfold commBound
  have hκ0 := unitMassScaledMollifier_nonneg' (d := d) hδ x
  positivity

/-- **The commutator pairing bound**: `|E[ρ · commOp(V)]| ≤ C ‖ρ‖₂ ∑ⱼ ‖Vⱼ‖₂`, uniformly in the scale
`δ ≤ 1`, on almost surely Lipschitz coefficients. -/
theorem abs_integral_mul_commOp_le (hd : 2 ≤ d) (lam : ℝ) {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} (hgood : ∀ᵐ w ∂Q, ∀ j k, LipschitzWith L fun y => w.1 y j k)
    {ρ : FieldPair d → ℝ} (hρm : Measurable ρ) (hρ : MemLp ρ 2 Q) {V : FieldPair d → Vec d}
    (hVm : Measurable V) (hV : ∀ j, MemLp (fun w => V w j) 2 Q) :
    |∫ w, ρ w * commOp hd lam (Calculus.unitMassScaledMollifier d δ) V w ∂Q| ≤
      commConst d lam L * Real.sqrt (∫ w, ρ w ^ 2 ∂Q) *
        ∑ j, Real.sqrt (∫ w, V w j ^ 2 ∂Q) := by
  set κ := Calculus.unitMassScaledMollifier d δ with hκdef
  set cB := commBound d lam δ L with hcBdef
  have hcB0 : ∀ x, 0 ≤ cB x := commBound_nonneg lam hδ L
  have hcBm : Measurable cB := (continuous_commBound d lam δ L).measurable
  have hcBi : Integrable cB := integrable_commBound lam hδ L
  have hVjm : ∀ j, Measurable fun w => V w j := fun j => (measurable_pi_apply j).comp hVm
  have hVa : ∀ j, MemLp (fun w => |V w j|) 2 Q := fun j => (hV j).abs
  -- The smoothed absolute fields.
  have hS := fun j => integral_sq_horizontalMollify_le hQ hcB0 hcBm hcBi
    (g := fun w => |V w j|) (continuous_abs.measurable.comp (hVjm j)) (hVa j)
  -- Almost sure integrability along orbits.
  have hint : ∀ j, ∀ᵐ w ∂Q, Integrable fun x => cB x * |V (translate x w) j| := fun j =>
    (integrable_prod_kernel_translate hQ hcBm hcBi (continuous_abs.measurable.comp (hVjm j))
      ((hVa j).integrable one_le_two)).prod_right_ae
  have hpt : ∀ᵐ w ∂Q, |commOp hd lam κ V w| ≤
      ∑ j, horizontalMollify cB (fun w' => |V w' j|) w := by
    filter_upwards [hgood, ae_all_iff.mpr hint] with w hw hwi
    unfold commOp
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine abs_integral_le_integral_abs.trans ?_
    unfold horizontalMollify
    refine integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hwi j)
      (ae_of_all _ fun x => ?_)
    show |commKernel hd lam κ w j x * V (translate x w) j| ≤ cB x * |V (translate x w) j|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_commKernel_le hd lam hδ hw j x) (abs_nonneg _)
  have hprod : ∀ j, Integrable (fun w => |ρ w| * horizontalMollify cB (fun w' => |V w' j|) w) Q :=
    fun j => hρ.abs.integrable_mul (hS j).1
  have hcm : ∫ x, cB x ≤ commConst d lam L := integral_commBound_le lam hδ hδ1 L
  have hm0 : 0 ≤ ∫ x, cB x := integral_nonneg hcB0
  calc |∫ w, ρ w * commOp hd lam κ V w ∂Q|
      ≤ ∫ w, |ρ w * commOp hd lam κ V w| ∂Q := abs_integral_le_integral_abs
    _ ≤ ∫ w, ∑ j, |ρ w| * horizontalMollify cB (fun w' => |V w' j|) w ∂Q := by
        refine integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _)
          (integrable_finset_sum _ fun j _ => hprod j) ?_
        filter_upwards [hpt] with w hw
        rw [abs_mul, ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ = ∑ j, ∫ w, |ρ w| * horizontalMollify cB (fun w' => |V w' j|) w ∂Q :=
        integral_finset_sum _ fun j _ => hprod j
    _ ≤ ∑ j, commConst d lam L * Real.sqrt (∫ w, ρ w ^ 2 ∂Q) *
          Real.sqrt (∫ w, V w j ^ 2 ∂Q) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 := abs_integral_mul_le_sqrt (f := fun w => |ρ w|)
          (g := horizontalMollify cB (fun w' => |V w' j|)) hρ.abs (hS j).1
        have hsq : ∀ u : FieldPair d → ℝ, ∫ w, |u w| ^ 2 ∂Q = ∫ w, u w ^ 2 ∂Q := fun u =>
          integral_congr_ae (ae_of_all _ fun w => sq_abs _)
        rw [hsq ρ] at h1
        have h2 : Real.sqrt (∫ w, horizontalMollify cB (fun w' => |V w' j|) w ^ 2 ∂Q) ≤
            (∫ x, cB x) * Real.sqrt (∫ w, V w j ^ 2 ∂Q) := by
          have h := (hS j).2
          rw [hsq (fun w => V w j)] at h
          calc Real.sqrt (∫ w, horizontalMollify cB (fun w' => |V w' j|) w ^ 2 ∂Q)
              ≤ Real.sqrt ((∫ x, cB x) ^ 2 * ∫ w, V w j ^ 2 ∂Q) := Real.sqrt_le_sqrt h
            _ = (∫ x, cB x) * Real.sqrt (∫ w, V w j ^ 2 ∂Q) := by
                rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm0]
        calc ∫ w, |ρ w| * horizontalMollify cB (fun w' => |V w' j|) w ∂Q
            ≤ |∫ w, |ρ w| * horizontalMollify cB (fun w' => |V w' j|) w ∂Q| := le_abs_self _
          _ ≤ Real.sqrt (∫ w, ρ w ^ 2 ∂Q) *
              Real.sqrt (∫ w, horizontalMollify cB (fun w' => |V w' j|) w ^ 2 ∂Q) := h1
          _ ≤ Real.sqrt (∫ w, ρ w ^ 2 ∂Q) * ((∫ x, cB x) * Real.sqrt (∫ w, V w j ^ 2 ∂Q)) :=
              mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
          _ ≤ Real.sqrt (∫ w, ρ w ^ 2 ∂Q) * (commConst d lam L * Real.sqrt (∫ w, V w j ^ 2 ∂Q)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcm (Real.sqrt_nonneg _))
                (Real.sqrt_nonneg _)
          _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]

/-- Smoothing by a signed integrable kernel preserves `L²`. -/
theorem memLp_horizontalMollify_signed {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {k : Vec d → ℝ} (hkm : Measurable k) (hki : Integrable k)
    {u : FieldPair d → ℝ} (hum : Measurable u) (hu : MemLp u 2 Q) :
    MemLp (horizontalMollify k u) 2 Q ∧
      ∫ w, horizontalMollify k u w ^ 2 ∂Q ≤ (∫ x, |k x|) ^ 2 * ∫ w, u w ^ 2 ∂Q := by
  have h := integral_sq_horizontalMollify_le hQ (k := fun x => |k x|) (fun x => abs_nonneg _)
    hkm.abs hki.abs (g := fun w => |u w|) hum.abs hu.abs
  have hpt : ∀ w, |horizontalMollify k u w| ≤ horizontalMollify (fun x => |k x|) (fun w => |u w|) w :=
    fun w => by
      unfold horizontalMollify
      refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
      exact integral_congr_ae (ae_of_all _ fun x => abs_mul _ _)
  have hm : Measurable (horizontalMollify k u) := measurable_horizontalMollify k hkm hum
  have hmem : MemLp (horizontalMollify k u) 2 Q :=
    h.1.of_le hm.aestronglyMeasurable (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact (hpt w).trans (le_abs_self _))
  refine ⟨hmem, ?_⟩
  have hsq : ∫ w, |u w| ^ 2 ∂Q = ∫ w, u w ^ 2 ∂Q := integral_congr_ae (ae_of_all _ fun w => sq_abs _)
  calc ∫ w, horizontalMollify k u w ^ 2 ∂Q ≤
        ∫ w, horizontalMollify (fun x => |k x|) (fun w => |u w|) w ^ 2 ∂Q := by
        refine integral_mono ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hmem)
          ((memLp_two_iff_integrable_sq h.1.aestronglyMeasurable).mp h.1) fun w => ?_
        have h1 := hpt w
        have h0 := abs_nonneg (horizontalMollify k u w)
        nlinarith [sq_abs (horizontalMollify k u w)]
    _ ≤ _ := by rw [← hsq]; exact h.2

/-! ## The smoothed equation -/

theorem reflectKernel_reflectKernel (κ : Vec d → ℝ) : reflectKernel (reflectKernel κ) = κ :=
  funext fun x => by simp [reflectKernel]

theorem coordinateDerivative_reflectKernel {κ : Vec d → ℝ} (hκ : Differentiable ℝ κ) (k : Fin d)
    (y : Vec d) :
    coordinateDerivative k (reflectKernel κ) y = -coordinateDerivative k κ (-y) := by
  have h : HasFDerivAt (fun x : Vec d => κ (-x)) ((fderiv ℝ κ (-y)).comp (-ContinuousLinearMap.id ℝ (Vec d))) y :=
    (hκ (-y)).hasFDerivAt.comp y (hasFDerivAt_id y).neg
  unfold coordinateDerivative reflectKernel
  rw [h.fderiv]
  simp

theorem reflectKernel_divKernel {κ : Vec d → ℝ} (hκ : Differentiable ℝ κ) (k : Fin d) :
    reflectKernel (divKernel κ k) = fun y => -reflectKernel (coordinateDerivative k κ) y := by
  funext y
  unfold reflectKernel divKernel
  rw [neg_neg, coordinateDerivative_reflectKernel hκ]

/-- The smoothed density `ρ^δ = S_{κ̃} ρ`. -/
def smoothDensity (d : ℕ) (δ : ℝ) (ρ : FieldPair d → ℝ) : FieldPair d → ℝ :=
  horizontalMollify (reflectKernel (Calculus.unitMassScaledMollifier d δ)) ρ

/-- Its horizontal gradient `Dρ^δ = S_{(∂κ)~} ρ`. -/
def smoothGrad (d : ℕ) (δ : ℝ) (ρ : FieldPair d → ℝ) (w : FieldPair d) : Vec d :=
  fun k => horizontalMollify (reflectKernel
    (coordinateDerivative k (Calculus.unitMassScaledMollifier d δ))) ρ w

theorem measurable_commOp (hd : 2 ≤ d) (lam : ℝ) {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    {V : FieldPair d → Vec d} (hVm : Measurable V) : Measurable (commOp hd lam κ V) := by
  unfold commOp
  refine Finset.measurable_sum _ fun j _ => ?_
  have hentry : ∀ i, Measurable fun p : FieldPair d × Vec d => p.1.1 0 j i := fun i =>
    ((((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j i).measurable).comp
      measurable_fst
  have hentryx : ∀ i, Measurable fun p : FieldPair d × Vec d => p.1.1 p.2 j i := fun i =>
    ((continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).matrix_elem
      j i).measurable
  have hκm : Measurable fun p : FieldPair d × Vec d => κ p.2 := hκ.continuous.measurable.comp measurable_snd
  have hκk : ∀ k, Measurable fun p : FieldPair d × Vec d => coordinateDerivative k κ p.2 := fun k =>
    ((hκ.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.comp measurable_snd
  have hfd : ∀ k, Measurable fun p : FieldPair d × Vec d =>
      fderiv ℝ (fun y => p.1.1 y j k) 0 (unitVector k) := fun k =>
    (measurable_fderiv_entry_zero j k (unitVector k)).comp measurable_fst
  have hker : Measurable fun p : FieldPair d × Vec d => commKernel hd lam κ p.1 j p.2 := by
    unfold commKernel
    exact (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      (hκm.mul (hfd k)).sub ((hκk k).mul ((hentry k).sub (hentryx k))))).add
      (measurable_const.mul (hκm.mul ((hentry _).sub (hentryx _))))
  have hV : Measurable fun p : FieldPair d × Vec d => V (translate p.2 p.1) j :=
    (measurable_pi_apply j).comp (hVm.comp
      (Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)))
  exact (hker.mul hV).stronglyMeasurable.integral_prod_right'.measurable

/-- `commOp` of an `L²` field is in `L²`, on almost surely Lipschitz coefficients. -/
theorem memLp_commOp (hd : 2 ≤ d) (lam : ℝ) {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {δ : ℝ} (hδ : 0 < δ) {L : ℝ≥0}
    (hgood : ∀ᵐ w ∂Q, ∀ j k, LipschitzWith L fun y => w.1 y j k) {V : FieldPair d → Vec d}
    (hVm : Measurable V) (hV : ∀ j, MemLp (fun w => V w j) 2 Q) :
    MemLp (commOp hd lam (Calculus.unitMassScaledMollifier d δ) V) 2 Q := by
  set cB := commBound d lam δ L with hcBdef
  have hcB0 : ∀ x, 0 ≤ cB x := commBound_nonneg lam hδ L
  have hcBm : Measurable cB := (continuous_commBound d lam δ L).measurable
  have hcBi : Integrable cB := integrable_commBound lam hδ L
  have hVjm : ∀ j, Measurable fun w => V w j := fun j => (measurable_pi_apply j).comp hVm
  have hS := fun j => integral_sq_horizontalMollify_le hQ hcB0 hcBm hcBi
    (g := fun w => |V w j|) (continuous_abs.measurable.comp (hVjm j)) (hV j).abs
  have hint : ∀ j, ∀ᵐ w ∂Q, Integrable fun x => cB x * |V (translate x w) j| := fun j =>
    (integrable_prod_kernel_translate hQ hcBm hcBi (continuous_abs.measurable.comp (hVjm j))
      (((hV j).abs).integrable one_le_two)).prod_right_ae
  have hdom : MemLp (fun w => ∑ j, horizontalMollify cB (fun w' => |V w' j|) w) 2 Q :=
    memLp_finset_sum _ fun j _ => (hS j).1
  refine hdom.of_le (measurable_commOp hd lam (contDiff_unitMassScaledMollifier δ)
    hVm).aestronglyMeasurable ?_
  filter_upwards [hgood, ae_all_iff.mpr hint] with w hw hwi
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  unfold commOp
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine abs_integral_le_integral_abs.trans ?_
  unfold horizontalMollify
  refine integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hwi j)
    (ae_of_all _ fun x => ?_)
  show |commKernel hd lam _ w j x * V (translate x w) j| ≤ cB x * |V (translate x w) j|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_commKernel_le hd lam hδ hw j x) (abs_nonneg _)

/-- On a coefficient with entries bounded by `K` and `L`-Lipschitz, the generator of a test is
bounded. -/
theorem abs_envGenerator_le_of_good (hd : 2 ≤ d) (lam : ℝ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) :
    ∃ M1 M2 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧ ∀ {K : ℝ} {L : ℝ≥0} (w : FieldPair d),
      (∀ x j k, |w.1 x j k| ≤ K) → (∀ j k, LipschitzWith L fun y => w.1 y j k) →
      |envGenerator hd lam F w| ≤ (1 / 2 : ℝ) * ∑ k : Fin d, ∑ _j : Fin d,
          (L * ‖unitVector (d := d) k‖ * M1 + K * M2) + |lam| * ∑ _j : Fin d, K * M1 := by
  obtain ⟨M0, M1, M2, hM1, hM2, -, hb1, hb2⟩ := hF.exists_bounds
  refine ⟨M1, M2, hM1, hM2, fun {K L} w hwB hwL => ?_⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hwB 0 ⟨0, by omega⟩ ⟨0, by omega⟩)
  have h1 : ∀ j, |horizontalDerivative j F w| ≤ M1 := fun j => hb1 w 0 j
  have h2 : ∀ j k, |horizontalDerivative k (horizontalDerivative j F) w| ≤ M2 := fun j k => by
    show |fderiv ℝ (orbit (EinsteinRelation.horizontalDerivative j F) w) 0 (unitVector k)| ≤ M2
    rw [orbit_horizontalDerivative]
    exact hb2 w 0 j k
  unfold envGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k _ => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => ?_))) (by norm_num)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (abs_coeffDeriv_le (hwL j k) 0) (h1 j) (abs_nonneg _)
        (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
    · rw [abs_mul]
      exact mul_le_mul (hwB 0 j k) (h2 j k) (abs_nonneg _) hK0
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)) (abs_nonneg _)
    rw [abs_mul]
    exact mul_le_mul (hwB 0 j _) (h1 j) (abs_nonneg _) hK0

theorem measurable_testFlux {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    Measurable (testFlux F) := by
  have hentry : ∀ j k : Fin d, Measurable fun w : FieldPair d => w.1 0 j k := fun j k =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
  exact Measurable.of_eval fun k => Finset.measurable_sum _ fun j _ =>
    (hentry j k).mul (hF.measurable_derivative j)

theorem measurable_testFluxDiv {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    Measurable (testFluxDiv F) := by
  have hentry : ∀ j k : Fin d, Measurable fun w : FieldPair d => w.1 0 j k := fun j k =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
  unfold testFluxDiv
  exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ =>
    ((measurable_fderiv_entry_zero j k _).mul (hF.measurable_derivative j)).add
      ((hentry j k).mul ((hF.horizontalDerivative j).measurable_derivative k))

theorem memLp_of_ae_bound' {Q : Measure (FieldPair d)} [IsFiniteMeasure Q] {g : FieldPair d → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ᵐ w ∂Q, |g w| ≤ C) (q : ℝ≥0∞) : MemLp g q Q :=
  MemLp.of_bound hg.aestronglyMeasurable C (hC.mono fun w hw => by rwa [Real.norm_eq_abs])

/-- The drift `(a e₁) · DF` of a test. -/
def testDrift (hd : 2 ≤ d) (F : FieldPair d → ℝ) (w : FieldPair d) : ℝ :=
  ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j F w

theorem horizontalMollify_neg_kernel (k : Vec d → ℝ) (u : FieldPair d → ℝ) (w : FieldPair d) :
    horizontalMollify (fun y => -k y) u w = -horizontalMollify k u w := by
  unfold horizontalMollify
  rw [← integral_neg]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

/-- The smoothed flux term: `E[ρ^δ D·(a DF)] = -∑ₖ E[Dₖρ^δ (a DF)ₖ]`. -/
theorem integral_smoothDensity_mul_testFluxDiv {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {ρ : FieldPair d → ℝ}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q)) {K : ℝ}
    (hgood : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), ∀ x j k, |w.1 x j k| ≤ K)
    {δ : ℝ} (hδ : 0 < δ) {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    ∫ w, smoothDensity d δ ρ w * testFluxDiv F w ∂(Carriers.reducedReferenceLaw Q) =
      -∑ k, ∫ w, smoothGrad d δ ρ w k * testFlux F w k ∂(Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  set κ := Calculus.unitMassScaledMollifier d δ with hκdef
  have hκs : ContDiff ℝ (⊤ : ℕ∞) κ := contDiff_unitMassScaledMollifier δ
  have hκc : HasCompactSupport κ := hasCompactSupport_unitMassScaledMollifier hδ
  have hκd : Differentiable ℝ κ := hκs.differentiable (by simp)
  have hrκm : Measurable (reflectKernel κ) := (contDiff_reflectKernel hκs).continuous.measurable
  have hrκi : Integrable (reflectKernel κ) := (contDiff_reflectKernel hκs).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_reflectKernel hκc)
  have hdkm : ∀ k, Measurable (divKernel κ k) := fun k => (continuous_divKernel hκs k).measurable
  have hdki : ∀ k, Integrable (divKernel κ k) := fun k =>
    (continuous_divKernel hκs k).integrable_of_hasCompactSupport (hasCompactSupport_divKernel hκc k)
  have hrdkm : ∀ k, Measurable (reflectKernel (divKernel κ k)) := fun k =>
    (hdkm k).comp measurable_neg
  have hrdki : ∀ k, Integrable (reflectKernel (divKernel κ k)) := fun k => (hdki k).comp_neg
  obtain ⟨M0, M1, M2, hM1, -, -, hb1, -⟩ := hF.exists_bounds
  have hhm := measurable_testFluxDiv hF
  have hh2 := memLp_testFluxDiv Q hQ hF 2
  have hVm := measurable_testFlux hF
  have hV2 : ∀ k, MemLp (fun w => testFlux F w k) 2 μ := fun k =>
    memLp_of_ae_bound' ((measurable_pi_apply k).comp hVm) (C := ∑ _j : Fin d, K * M1)
      (by
        filter_upwards [hgood] with w hw
        unfold testFlux
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (hw 0 j k) (hb1 w 0 j) (abs_nonneg _)
          ((abs_nonneg _).trans (hw 0 j k))) 2
  -- Step a: move the smoothing onto `h`.
  have ha : ∫ w, smoothDensity d δ ρ w * testFluxDiv F w ∂μ =
      ∫ w, ρ w * horizontalMollify κ (testFluxDiv F) w ∂μ := by
    have h := integral_horizontalMollify_mul_eq_L2 hQ hrκm hrκi hρm hρ hhm hh2
    rw [reflectKernel_reflectKernel] at h
    exact h
  -- Step b: the smoothed divergence identity.
  have hb := ae_horizontalMollify_eq_of_hasWeakHorizontalDivergence hQ hκs hκc hVm
    (fun k => (hV2 k).integrable one_le_two) hhm (hh2.integrable one_le_two)
    (hasWeakHorizontalDivergence_testFlux Q hQ hF)
  have hSV2 : ∀ k, MemLp (horizontalMollify (divKernel κ k) (fun w => testFlux F w k)) 2 μ :=
    fun k => (memLp_horizontalMollify_signed hQ (hdkm k) (hdki k)
      ((measurable_pi_apply k).comp hVm) (hV2 k)).1
  have hb' : ∫ w, ρ w * horizontalMollify κ (testFluxDiv F) w ∂μ =
      ∑ k, ∫ w, ρ w * horizontalMollify (divKernel κ k) (fun w => testFlux F w k) w ∂μ := by
    have hint : ∀ k, Integrable (fun w => ρ w *
        horizontalMollify (divKernel κ k) (fun w => testFlux F w k) w) μ := fun k =>
      hρ.integrable_mul (hSV2 k)
    rw [← integral_finset_sum _ fun k _ => hint k]
    refine integral_congr_ae (hb.mono fun w hw => ?_)
    simp only [hw, Finset.mul_sum]
  -- Steps d, e: back onto `ρ`.
  have hde : ∀ k, ∫ w, ρ w * horizontalMollify (divKernel κ k) (fun w => testFlux F w k) w ∂μ =
      -∫ w, smoothGrad d δ ρ w k * testFlux F w k ∂μ := by
    intro k
    have h := integral_horizontalMollify_mul_eq_L2 hQ (hrdkm k) (hrdki k) hρm hρ
      (W := fun w => testFlux F w k) ((measurable_pi_apply k).comp hVm) (hV2 k)
    rw [reflectKernel_reflectKernel] at h
    rw [← h, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show horizontalMollify (reflectKernel (divKernel κ k)) ρ w * testFlux F w k =
      -(horizontalMollify (reflectKernel (coordinateDerivative k κ)) ρ w * testFlux F w k)
    rw [reflectKernel_divKernel hκd k, horizontalMollify_neg_kernel]
    ring
  rw [ha, hb', Finset.sum_congr rfl fun k _ => hde k, Finset.sum_neg_distrib]

/-- **The smoothed equation.** If `ρ ∈ L²` solves `μ₀ E[ρG] - E[ρ L G] = E[fG]` for every test
`G`, then for every test `F`, with `ρ^δ = S_{κ̃} ρ` and `Dρ^δ = smoothGrad`,
`μ₀ E[ρ^δ F] + ½ ∑ₖ E[Dₖρ^δ (a DF)ₖ] - λ E[ρ^δ (a e₁)·DF] - E[ρ commOp(DF)] = E[f^δ F]`. -/
theorem smoothed_equation (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {μ0 : ℝ} {ρ f : FieldPair d → ℝ}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q))
    (hfm : Measurable f) (hf : MemLp f 2 (Carriers.reducedReferenceLaw Q))
    (heq : ∀ G : FieldPair d → ℝ, IsHorizontalTest G →
      μ0 * (∫ w, ρ w * G w ∂(Carriers.reducedReferenceLaw Q)) -
        ∫ w, ρ w * envGenerator hd lam G w ∂(Carriers.reducedReferenceLaw Q) =
          ∫ w, f w * G w ∂(Carriers.reducedReferenceLaw Q))
    {K : ℝ} {L : ℝ≥0}
    (hgood : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), (∀ x j k, |w.1 x j k| ≤ K) ∧
      ∀ j k, LipschitzWith L fun y => w.1 y j k)
    {δ : ℝ} (hδ : 0 < δ) {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    μ0 * (∫ w, smoothDensity d δ ρ w * F w ∂(Carriers.reducedReferenceLaw Q)) +
        (1 / 2 : ℝ) * ∑ k, (∫ w, smoothGrad d δ ρ w k * testFlux F w k
          ∂(Carriers.reducedReferenceLaw Q)) -
        lam * (∫ w, smoothDensity d δ ρ w * testDrift hd F w ∂(Carriers.reducedReferenceLaw Q)) -
        (∫ w, ρ w * commOp hd lam (Calculus.unitMassScaledMollifier d δ)
          (fun w' j => horizontalDerivative j F w') w ∂(Carriers.reducedReferenceLaw Q)) =
      ∫ w, smoothDensity d δ f w * F w ∂(Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  set κ := Calculus.unitMassScaledMollifier d δ with hκdef
  have hκs : ContDiff ℝ (⊤ : ℕ∞) κ := contDiff_unitMassScaledMollifier δ
  have hκc : HasCompactSupport κ := hasCompactSupport_unitMassScaledMollifier hδ
  have hκm : Measurable κ := hκs.continuous.measurable
  have hκi : Integrable κ := hκs.continuous.integrable_of_hasCompactSupport hκc
  have hrκm : Measurable (reflectKernel κ) := (contDiff_reflectKernel hκs).continuous.measurable
  have hrκi : Integrable (reflectKernel κ) :=
    (contDiff_reflectKernel hκs).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_reflectKernel hκc)
  obtain ⟨B, -, hB⟩ := hF.bound_orbit
  have hFB : ∀ w, |F w| ≤ B := fun w => by simpa using hB w 0
  have hFm : Measurable F := hF.1
  have hF2 : MemLp F 2 μ := memLp_of_ae_bound' hFm (ae_of_all _ hFB) 2
  have hSF : IsHorizontalTest (horizontalMollify κ F) :=
    Correctors.isHorizontalTest_horizontalMollify κ hκs hκc F hFm ⟨B, hFB⟩
  have h1 := heq _ hSF
  -- Adjoints for the zeroth-order terms.
  have hA : ∫ w, ρ w * horizontalMollify κ F w ∂μ = ∫ w, smoothDensity d δ ρ w * F w ∂μ := by
    have h := integral_horizontalMollify_mul_eq_L2 hQ hrκm hrκi hρm hρ hFm hF2
    rw [reflectKernel_reflectKernel] at h
    exact h.symm
  have hB' : ∫ w, f w * horizontalMollify κ F w ∂μ = ∫ w, smoothDensity d δ f w * F w ∂μ := by
    have h := integral_horizontalMollify_mul_eq_L2 hQ hrκm hrκi hfm hf hFm hF2
    rw [reflectKernel_reflectKernel] at h
    exact h.symm
  -- The generator of the smoothed test, through the commutator.
  obtain ⟨M1, M2, hM1, hM2, hEB⟩ := abs_envGenerator_le_of_good hd lam hF
  have hEm : Measurable (envGenerator hd lam F) := measurable_envGenerator hd lam hF
  have hE2 : MemLp (envGenerator hd lam F) 2 μ :=
    memLp_of_ae_bound' hEm (hgood.mono fun w hw => hEB w hw.1 hw.2) 2
  have hSE := (memLp_horizontalMollify_signed hQ hκm hκi hEm hE2).1
  have hDFm : Measurable fun w' : FieldPair d => fun j => horizontalDerivative j F w' :=
    Measurable.of_eval fun j => hF.measurable_derivative j
  have hDF2 : ∀ j, MemLp (fun w => horizontalDerivative j F w) 2 μ := fun j =>
    (hF.memLp_derivative μ 2 j)
  have hC2 := memLp_commOp hd lam hQ hδ (hgood.mono fun w hw => hw.2) hDFm hDF2
  have hcomm : ∫ w, ρ w * envGenerator hd lam (horizontalMollify κ F) w ∂μ =
      (∫ w, ρ w * horizontalMollify κ (envGenerator hd lam F) w ∂μ) +
        ∫ w, ρ w * commOp hd lam κ (fun w' j => horizontalDerivative j F w') w ∂μ := by
    have hI1 : Integrable (fun w => ρ w * horizontalMollify κ (envGenerator hd lam F) w) μ :=
      hρ.integrable_mul hSE
    have hI2 : Integrable (fun w => ρ w *
        commOp hd lam κ (fun w' j => horizontalDerivative j F w') w) μ := hρ.integrable_mul hC2
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (hgood.mono fun w hw => ?_)
    have h := envGenerator_horizontalMollify_sub hd lam hκs hκc hF hw.1 hw.2
    show ρ w * envGenerator hd lam (horizontalMollify κ F) w =
      ρ w * horizontalMollify κ (envGenerator hd lam F) w +
        ρ w * commOp hd lam κ (fun w' j => horizontalDerivative j F w') w
    rw [← mul_add, ← h]
    ring
  have hD : ∫ w, ρ w * horizontalMollify κ (envGenerator hd lam F) w ∂μ =
      ∫ w, smoothDensity d δ ρ w * envGenerator hd lam F w ∂μ := by
    have h := integral_horizontalMollify_mul_eq_L2 hQ hrκm hrκi hρm hρ hEm hE2
    rw [reflectKernel_reflectKernel] at h
    exact h.symm
  -- The generator of `F`, split into the flux divergence and the drift.
  have hρδ := (memLp_horizontalMollify_signed hQ hrκm hrκi hρm hρ).1
  have hh2 := memLp_testFluxDiv Q hQ hF 2
  have hXm : Measurable (testDrift hd F) := by
    have hentry : ∀ j k : Fin d, Measurable fun w : FieldPair d => w.1 0 j k := fun j k =>
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
    unfold testDrift
    exact Finset.measurable_sum _ fun j _ => (hentry j _).mul (hF.measurable_derivative j)
  obtain ⟨M0', M1', M2', -, -, -, hb1, -⟩ := hF.exists_bounds
  have hX2 : MemLp (testDrift hd F) 2 μ :=
    memLp_of_ae_bound' hXm (C := ∑ _j : Fin d, K * M1') (hgood.mono fun w hw => by
      unfold testDrift
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (hw.1 0 j _) (hb1 w 0 j) (abs_nonneg _)
        ((abs_nonneg _).trans (hw.1 0 j j))) 2
  have hsplit : ∫ w, smoothDensity d δ ρ w * envGenerator hd lam F w ∂μ =
      (1 / 2 : ℝ) * (∫ w, smoothDensity d δ ρ w * testFluxDiv F w ∂μ) +
        lam * ∫ w, smoothDensity d δ ρ w * testDrift hd F w ∂μ := by
    have hJ1 : Integrable (fun w => 1 / 2 * (smoothDensity d δ ρ w * testFluxDiv F w)) μ :=
      (hρδ.integrable_mul hh2).const_mul _
    have hJ2 : Integrable (fun w => lam * (smoothDensity d δ ρ w * testDrift hd F w)) μ :=
      (hρδ.integrable_mul hX2).const_mul _
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hJ1 hJ2]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show smoothDensity d δ ρ w * envGenerator hd lam F w =
      1 / 2 * (smoothDensity d δ ρ w * testFluxDiv F w) +
        lam * (smoothDensity d δ ρ w * testDrift hd F w)
    rw [envGenerator_eq_testFluxDiv]
    unfold testDrift
    ring
  have hflux := integral_smoothDensity_mul_testFluxDiv Q hQ hρm hρ
    (hgood.mono fun w hw => hw.1) hδ hF
  rw [hA, hB', hcomm, hD, hsplit, hflux] at h1
  linarith

/-! ## The smoothed density is in `H¹` -/

theorem memLp_smoothDensity {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ρ : FieldPair d → ℝ} (hρm : Measurable ρ) (hρ : MemLp ρ 2 Q)
    {δ : ℝ} (hδ : 0 < δ) : MemLp (smoothDensity d δ ρ) 2 Q :=
  (memLp_horizontalMollify_signed hQ
    (contDiff_reflectKernel (contDiff_unitMassScaledMollifier δ)).continuous.measurable
    ((contDiff_reflectKernel (contDiff_unitMassScaledMollifier δ)).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_reflectKernel (hasCompactSupport_unitMassScaledMollifier hδ))) hρm hρ).1

theorem measurable_smoothDensity {ρ : FieldPair d → ℝ} (hρm : Measurable ρ) (δ : ℝ) :
    Measurable (smoothDensity d δ ρ) :=
  measurable_horizontalMollify _
    (contDiff_reflectKernel (contDiff_unitMassScaledMollifier δ)).continuous.measurable hρm

theorem kernel_reflect_deriv_props {δ : ℝ} (hδ : 0 < δ) (k : Fin d) :
    Measurable (reflectKernel (coordinateDerivative k (Calculus.unitMassScaledMollifier d δ))) ∧
      Integrable (reflectKernel (coordinateDerivative k (Calculus.unitMassScaledMollifier d δ))) := by
  have hc := continuous_coordinateDerivative_unitMassScaledMollifier (d := d) δ k
  have hcc := hasCompactSupport_coordinateDerivative_unitMassScaledMollifier (d := d) hδ k
  refine ⟨hc.measurable.comp measurable_neg, ?_⟩
  exact (hc.integrable_of_hasCompactSupport hcc).comp_neg

theorem memLp_smoothGrad {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ρ : FieldPair d → ℝ} (hρm : Measurable ρ) (hρ : MemLp ρ 2 Q)
    {δ : ℝ} (hδ : 0 < δ) (k : Fin d) : MemLp (fun w => smoothGrad d δ ρ w k) 2 Q :=
  (memLp_horizontalMollify_signed hQ (kernel_reflect_deriv_props hδ k).1
    (kernel_reflect_deriv_props hδ k).2 hρm hρ).1

theorem measurable_smoothGrad {ρ : FieldPair d → ℝ} (hρm : Measurable ρ) {δ : ℝ} (hδ : 0 < δ) :
    Measurable (smoothGrad d δ ρ) :=
  Measurable.of_eval fun k =>
    measurable_horizontalMollify _ (kernel_reflect_deriv_props hδ k).1 hρm

/-- The test identity behind the weak gradient of `smoothDensity`. -/
theorem integral_smoothDensity_mul_derivative {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ρ : FieldPair d → ℝ} (hρm : Measurable ρ)
    (hρ : MemLp ρ 2 Q) {δ : ℝ} (hδ : 0 < δ) (i : Fin d) {K : FieldPair d → ℝ}
    (hK : IsHorizontalTest K) :
    (∫ ω, smoothDensity d δ ρ ω * horizontalDerivative i K ω ∂Q) =
      -(∫ ω, smoothGrad d δ ρ ω i * K ω ∂Q) := by
  set κ := Calculus.unitMassScaledMollifier d δ with hκdef
  have hκs : ContDiff ℝ (⊤ : ℕ∞) κ := contDiff_unitMassScaledMollifier δ
  have hκc : HasCompactSupport κ := hasCompactSupport_unitMassScaledMollifier hδ
  have hrκm : Measurable (reflectKernel κ) := (contDiff_reflectKernel hκs).continuous.measurable
  have hrκi : Integrable (reflectKernel κ) :=
    (contDiff_reflectKernel hκs).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_reflectKernel hκc)
  obtain ⟨B, -, hB⟩ := hK.bound_orbit
  have hKB : ∀ ω, |K ω| ≤ B := fun ω => by simpa using hB ω 0
  have hK2 : MemLp K 2 Q := memLp_of_ae_bound' hK.1 (ae_of_all _ hKB) 2
  have hDK2 : MemLp (horizontalDerivative i K) 2 Q := hK.memLp_derivative Q 2 i
  have hDKm := hK.measurable_derivative i
  have h1 := integral_horizontalMollify_mul_eq_L2 hQ hrκm hrκi hρm hρ hDKm hDK2
  rw [reflectKernel_reflectKernel] at h1
  have h2 : ∀ ω, horizontalMollify κ (horizontalDerivative i K) ω =
      -horizontalMollify (coordinateDerivative i κ) K ω := fun ω => by
    rw [← horizontalDerivative_horizontalMollify_eq hκs hκc hK i ω,
      Correctors.horizontalMollify_horizontalDerivative_formula hκs hκc hK.1 ⟨B, hKB⟩ i ω]
    rfl
  have hk := kernel_reflect_deriv_props (d := d) hδ i
  have h3 := integral_horizontalMollify_mul_eq_L2 hQ hk.1 hk.2 hρm hρ hK.1 hK2
  rw [reflectKernel_reflectKernel] at h3
  show (∫ ω, horizontalMollify (reflectKernel κ) ρ ω * horizontalDerivative i K ω ∂Q) =
    -(∫ ω, horizontalMollify (reflectKernel (coordinateDerivative i κ)) ρ ω * K ω ∂Q)
  rw [h1, h3, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  show ρ ω * horizontalMollify κ (horizontalDerivative i K) ω =
    -(ρ ω * horizontalMollify (coordinateDerivative i κ) K ω)
  rw [h2]
  ring

/-- A weak horizontal gradient from the identity against concrete horizontal tests. -/
theorem hasWeakHorizontalGradient_of_tests {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} {V : FieldPair d → Vec d} (hum : Measurable u)
    (hu : MemLp u 2 Q) (hVm : Measurable V) (hV : ∀ i, MemLp (fun w => V w i) 2 Q)
    (hcore : ∀ i, ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, V ω i * K ω ∂Q)) :
    HasWeakHorizontalGradient Q hQ u V := by
  refine ⟨hu.integrable one_le_two, fun i => (hV i).integrable one_le_two,
    fun i F G hFs hG => ?_⟩
  have h := Calculus.integral_chain_smooth hQ (g := id) contDiff_id (L := 1)
    (fun x => by simp) hum (hu.integrable one_le_two)
    ((measurable_pi_apply i).comp hVm) ((hV i).integrable one_le_two) i (hcore i) hFs hG
  simpa using h

/-- `smoothGrad` is the weak horizontal gradient of `smoothDensity`. -/
theorem hasWeakHorizontalGradient_smoothDensity {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ρ : FieldPair d → ℝ} (hρm : Measurable ρ)
    (hρ : MemLp ρ 2 Q) {δ : ℝ} (hδ : 0 < δ) :
    HasWeakHorizontalGradient Q hQ (smoothDensity d δ ρ) (smoothGrad d δ ρ) :=
  hasWeakHorizontalGradient_of_tests hQ (measurable_smoothDensity hρm δ)
    (memLp_smoothDensity hQ hρm hρ hδ) (measurable_smoothGrad hρm hδ)
    (memLp_smoothGrad hQ hρm hρ hδ) fun i _ hK =>
      integral_smoothDensity_mul_derivative hQ hρm hρ hδ i hK

/-- **Approximation by horizontal tests** (non-local version of `exists_local_test_approximation`). -/
theorem exists_test_approximation {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞)
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df)
    (hfq : MemLp f q Q) (hDfq : ∀ i, MemLp (fun w => Df w i) q Q)
    (hfm : Measurable f) (hDfm : Measurable Df) :
    ∃ (F : ℕ → FieldPair d → ℝ) (G : ℕ → FieldPair d → Vec d),
      (∀ n, IsHorizontalTest (F n)) ∧
      (∀ n, Measurable (G n)) ∧
      (∀ n, ∀ᵐ w ∂Q, ∀ i, horizontalDerivative i (F n) w = G n w i) ∧
      (∀ n, MemLp (fun w => F n w - f w) q Q) ∧
      Tendsto (fun n => eLpNorm (fun w => F n w - f w) q Q) atTop (𝓝 0) ∧
      (∀ n i, MemLp (fun w => G n w i - Df w i) q Q) ∧
      ∀ i, Tendsto (fun n => eLpNorm (fun w => G n w i - Df w i) q Q) atTop (𝓝 0) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  have hDim : ∀ i, Measurable fun w => Df w i := fun i => (measurable_pi_apply i).comp hDfm
  set δ : ℕ → ℝ≥0∞ := fun n => ((n : ℝ≥0∞) + 1)⁻¹ with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => ENNReal.inv_pos.mpr (by simp)
  have hδtop : ∀ n, δ n < ⊤ := fun n => by
    simp only [hδdef, ENNReal.inv_lt_top]
    exact lt_of_lt_of_le zero_lt_one le_add_self
  -- The truncated functions and their weak gradients.
  set u : ℕ → FieldPair d → ℝ := fun m w => softTruncation (m : ℝ) (f w) with hudef
  set v : ℕ → Fin d → FieldPair d → ℝ := fun m i w => softTruncationDeriv (m : ℝ) (f w) * Df w i
    with hvdef
  have hum : ∀ m, Measurable (u m) := fun m => (measurable_softTruncation _).comp hfm
  have hvm : ∀ m i, Measurable (v m i) := fun m i =>
    ((measurable_softTruncationDeriv _).comp hfm).mul (hDim i)
  have hvq : ∀ m i, MemLp (v m i) q Q := fun m i =>
    (hDfq i).of_le (hvm m i).aestronglyMeasurable (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_softTruncationDeriv_le_one _ _))
  have huq : ∀ m : ℕ, 0 < m → MemLp (u m) q Q := fun m hm =>
    MemLp.of_bound (hum m).aestronglyMeasurable (m : ℝ) (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs]; exact abs_softTruncation_le_level (by exact_mod_cast hm) _)
  -- Step 1: the truncation level.
  have hT : ∀ n, ∃ m : ℕ, 0 < m ∧
      eLpNorm (fun w => u m w - f w) q Q ≤ δ n ∧
      ∀ i, eLpNorm (fun w => v m i w - Df w i) q Q ≤ δ n := by
    intro n
    have h1 := tendsto_eLpNorm_softTruncation_sub hq0 hq hfq hfm
    have h2 : ∀ i, Tendsto (fun m : ℕ => eLpNorm (fun w => v m i w - Df w i) q Q) atTop (𝓝 0) := by
      intro i
      refine (tendsto_eLpNorm_softTruncationDeriv_error hq0 hq (hDfq i) hfm (hDim i)).congr
        fun m => ?_
      rw [← eLpNorm_neg]
      congr 1
      funext w
      simp only [hvdef, Pi.neg_apply]
      ring
    have e1 := (ENNReal.tendsto_nhds_zero.mp h1) (δ n) (hδpos n)
    have e2 : ∀ᶠ m in atTop, ∀ i, eLpNorm (fun w => v m i w - Df w i) q Q ≤ δ n :=
      Filter.eventually_all.mpr fun i => (ENNReal.tendsto_nhds_zero.mp (h2 i)) (δ n) (hδpos n)
    obtain ⟨m, hm0, hm1, hm2⟩ := ((eventually_gt_atTop 0).and (e1.and e2)).exists
    exact ⟨m, hm0, hm1, hm2⟩
  choose m hm0 hmu hmv using hT
  -- Step 2: the mollification scale.
  have hE : ∀ n, ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      eLpNorm (fun w => horizontalMollify (Calculus.unitMassScaledMollifier d ε) (u (m n)) w -
        u (m n) w) q Q ≤ δ n ∧
      ∀ i, eLpNorm (fun w => horizontalMollify (Calculus.unitMassScaledMollifier d ε)
        (v (m n) i) w - v (m n) i w) q Q ≤ δ n := by
    intro n
    have h1 := Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ q hq
      (hum (m n)) (huq (m n) (hm0 n))
    have h2 := fun i => Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ q hq
      (hvm (m n) i) (hvq (m n) i)
    have e1 := (ENNReal.tendsto_nhds_zero.mp h1) (δ n) (hδpos n)
    have e2 := Filter.eventually_all.mpr fun i => (ENNReal.tendsto_nhds_zero.mp (h2 i)) (δ n)
      (hδpos n)
    have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo 0 1 :=
      Ioo_mem_nhdsGT one_pos
    obtain ⟨ε, hε, h1', h2'⟩ := (e3.and (e1.and e2)).exists
    exact ⟨ε, hε.1, hε.2.le, h1', h2'⟩
  choose ε hε0 hεr hεu hεv using hE
  have hε1 : ∀ n, ε n ≤ 1 := hεr
  set κ : ℕ → Vec d → ℝ := fun n => Calculus.unitMassScaledMollifier d (ε n) with hκdef
  have hκm : ∀ n, Measurable (κ n) := fun n =>
    (contDiff_unitMassScaledMollifier (ε n)).continuous.measurable
  have hSum : ∀ n, Measurable (horizontalMollify (κ n) (u (m n))) := fun n =>
    measurable_horizontalMollify (κ n) (hκm n) (hum (m n))
  have hSvm : ∀ n i, Measurable (horizontalMollify (κ n) (v (m n) i)) := fun n i =>
    measurable_horizontalMollify (κ n) (hκm n) (hvm (m n) i)
  have hSu : ∀ n, MemLp (fun w => horizontalMollify (κ n) (u (m n)) w - u (m n) w) q Q :=
    fun n => (hεu n).trans_lt (hδtop n)
  have hSvm' : ∀ n, Measurable fun w i => horizontalMollify (κ n) (v (m n) i) w := fun n =>
    Measurable.of_eval fun i => hSvm n i
  have hSv : ∀ n i, MemLp (fun w => horizontalMollify (κ n) (v (m n) i) w - v (m n) i w) q Q :=
    fun n i => (hεv n i).trans_lt (hδtop n)
  refine ⟨fun n => horizontalMollify (κ n) (u (m n)),
    fun n w i => horizontalMollify (κ n) (v (m n) i) w, fun n => ?_, fun n => ?_,
    fun n => ?_, fun n => ?_, ?_, fun n i => ?_, fun i => ?_⟩
  · exact Correctors.isHorizontalTest_horizontalMollify (κ n)
      (contDiff_unitMassScaledMollifier (ε n)) (hasCompactSupport_unitMassScaledMollifier (hε0 n))
      (u (m n)) (hum (m n)) ⟨(m n : ℝ), fun w =>
        abs_softTruncation_le_level (by exact_mod_cast hm0 n) _⟩
  · exact hSvm' n
  · have hchain := hasWeakHorizontalGradient_softTruncation hQ (m n : ℝ) hf
    rw [ae_all_iff]
    intro i
    have hfi : Integrable f Q := hf.1
    have hui : Integrable (u (m n)) Q := (huq (m n) (hm0 n)).integrable hq1
    have hvi : Integrable (v (m n) i) Q := (hvq (m n) i).integrable hq1
    exact Calculus.ae_orbit_derivative_mollify_eq hQ (hε0 n) (hε1 n) (hum (m n)) hui
      (hvm (m n) i) hvi i fun K hK => Calculus.weakPairing_core hchain i hK
  · have e : (fun w => horizontalMollify (κ n) (u (m n)) w - f w) =
        fun w => (horizontalMollify (κ n) (u (m n)) w - u (m n) w) + (u (m n) w - f w) :=
      funext fun w => by ring
    rw [e]
    exact (hSu n).add ((huq (m n) (hm0 n)).sub hfq)
  · refine tendsto_of_le_two_mul_inv fun n => ?_
    refine (eLpNorm_sub_le_of_split hq1 (hSum n).aestronglyMeasurable
      (hum (m n)).aestronglyMeasurable hfm.aestronglyMeasurable).trans ?_
    rw [two_mul]
    exact add_le_add (hεu n) (hmu n)
  · have e : (fun w => horizontalMollify (κ n) (v (m n) i) w - Df w i) =
        fun w => (horizontalMollify (κ n) (v (m n) i) w - v (m n) i w) + (v (m n) i w - Df w i) :=
      funext fun w => by ring
    rw [e]
    exact (hSv n i).add ((hvq (m n) i).sub (hDfq i))
  · refine tendsto_of_le_two_mul_inv fun n => ?_
    refine (eLpNorm_sub_le_of_split hq1 (hSvm n i).aestronglyMeasurable
      (hvm (m n) i).aestronglyMeasurable (hDim i).aestronglyMeasurable).trans ?_
    rw [two_mul]
    exact add_le_add (hεv n i) (hmv n i)

/-! ## Extension of the smoothed equation to `H¹` pairs -/

/-- Changing an observable on a null set changes it on a null set of every orbit, for almost every
environment. -/
theorem ae_ae_translate_eq {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u v : FieldPair d → ℝ} (hum : Measurable u) (hvm : Measurable v)
    (huv : u =ᵐ[Q] v) :
    ∀ᵐ w ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)), u (translate x w) = v (translate x w) := by
  have hT : Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
    Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)
  set S : Set (FieldPair d × Vec d) := {p | u (translate p.2 p.1) ≠ v (translate p.2 p.1)}
    with hSdef
  have hS : MeasurableSet S := (measurableSet_eq_fun (hum.comp hT) (hvm.comp hT)).compl
  have hslice : ∀ x : Vec d, Q ((fun w => (w, x)) ⁻¹' S) = 0 := by
    intro x
    have hpre : (fun w => (w, x)) ⁻¹' S = translate x ⁻¹' {w | u w ≠ v w} := rfl
    have hm : MeasurableSet {w : FieldPair d | u w ≠ v w} := (measurableSet_eq_fun hum hvm).compl
    rw [hpre, ← Measure.map_apply (Probability.measurable_translate x) hm, hQ x]
    exact ae_iff.mp huv
  have hprod : (Q.prod volume) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    simp only [hslice, lintegral_zero]
  have h := Measure.ae_ae_of_ae_prod (μ := Q) (ν := (volume : Measure (Vec d)))
    (p := fun p => u (translate p.2 p.1) = v (translate p.2 p.1)) (by
      rw [ae_iff]
      exact hprod)
  exact h

theorem commOp_congr_ae (hd : 2 ≤ d) (lam : ℝ) {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (κ : Vec d → ℝ) {V W : FieldPair d → Vec d} (hVm : Measurable V)
    (hWm : Measurable W) (hVW : ∀ᵐ w ∂Q, ∀ j, V w j = W w j) :
    ∀ᵐ w ∂Q, commOp hd lam κ V w = commOp hd lam κ W w := by
  have hj : ∀ j, ∀ᵐ w ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      V (translate x w) j = W (translate x w) j := fun j =>
    ae_ae_translate_eq hQ ((measurable_pi_apply j).comp hVm) ((measurable_pi_apply j).comp hWm)
      (hVW.mono fun w hw => hw j)
  filter_upwards [ae_all_iff.mpr hj] with w hw
  unfold commOp
  exact Finset.sum_congr rfl fun j _ => integral_congr_ae ((hw j).mono fun x hx => by
    simp only [hx])

theorem commOp_sub_ae (hd : 2 ≤ d) (lam : ℝ) {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {δ : ℝ} (hδ : 0 < δ) {L : ℝ≥0}
    (hgood : ∀ᵐ w ∂Q, ∀ j k, LipschitzWith L fun y => w.1 y j k) {V W : FieldPair d → Vec d}
    (hVm : Measurable V) (hWm : Measurable W) (hV : ∀ j, MemLp (fun w => V w j) 2 Q)
    (hW : ∀ j, MemLp (fun w => W w j) 2 Q) :
    ∀ᵐ w ∂Q, commOp hd lam (Calculus.unitMassScaledMollifier d δ) (fun w' j => V w' j - W w' j) w =
      commOp hd lam (Calculus.unitMassScaledMollifier d δ) V w -
        commOp hd lam (Calculus.unitMassScaledMollifier d δ) W w := by
  set cB := commBound d lam δ L with hcBdef
  have hcBm : Measurable cB := (continuous_commBound d lam δ L).measurable
  have hcBi : Integrable cB := integrable_commBound lam hδ L
  have hint : ∀ (U : FieldPair d → Vec d), Measurable U → (∀ j, MemLp (fun w => U w j) 2 Q) →
      ∀ j, ∀ᵐ w ∂Q, Integrable fun x => cB x * |U (translate x w) j| := fun U hUm hU j =>
    (integrable_prod_kernel_translate hQ hcBm hcBi
      (continuous_abs.measurable.comp ((measurable_pi_apply j).comp hUm))
      (((hU j).abs).integrable one_le_two)).prod_right_ae
  have hker : ∀ (U : FieldPair d → Vec d), Measurable U → ∀ w, (∀ j k, LipschitzWith L
      fun y => w.1 y j k) → ∀ j, Integrable (fun x => cB x * |U (translate x w) j|) →
      Integrable fun x => commKernel hd lam (Calculus.unitMassScaledMollifier d δ) w j x *
        U (translate x w) j := by
    intro U hUm w hw j hi
    have hkm : Measurable fun x => commKernel hd lam (Calculus.unitMassScaledMollifier d δ) w j x := by
      have hmeas := measurable_commOp hd lam (contDiff_unitMassScaledMollifier δ) hUm
      unfold commKernel
      have hκ := (contDiff_unitMassScaledMollifier (d := d) δ).continuous
      have hent : ∀ i, Continuous fun x : Vec d => w.1 x j i := fun i =>
        (continuous_apply i).comp ((continuous_apply j).comp w.1.continuous)
      exact (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
        (hκ.measurable.mul measurable_const).sub
          ((continuous_coordinateDerivative_unitMassScaledMollifier δ k).measurable.mul
            (measurable_const.sub (hent k).measurable)))).add
        (measurable_const.mul (hκ.measurable.mul (measurable_const.sub (hent _).measurable)))
    refine hi.mono' (hkm.mul ((measurable_pi_apply j).comp (hUm.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))))).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_commKernel_le hd lam hδ hw j x) (abs_nonneg _)
  filter_upwards [hgood, ae_all_iff.mpr (hint V hVm hV), ae_all_iff.mpr (hint W hWm hW)]
    with w hw hiV hiW
  unfold commOp
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (hker V hVm w hw j (hiV j)) (hker W hWm w hw j (hiW j))]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

theorem tendsto_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : ℕ → Ω → ℝ} (hg : ∀ n, MemLp (g n) 2 μ)
    (h : Tendsto (fun n => eLpNorm (g n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (∫ a, g n a ^ 2 ∂μ)) atTop (𝓝 0) := by
  have e : ∀ n, Real.sqrt (∫ a, g n a ^ 2 ∂μ) = (eLpNorm (g n) 2 μ).toReal := fun n => by
    rw [(hg n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    congr 1
    · refine integral_congr_ae (ae_of_all _ fun a => ?_)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    · simp
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h2
  exact h2.congr fun n => (e n).symm

theorem tendsto_integral_mul_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {a : Ω → ℝ}
    (ha : MemLp a 2 μ) {b : ℕ → Ω → ℝ} (hb : ∀ n, MemLp (b n) 2 μ)
    (h : Tendsto (fun n => Real.sqrt (∫ x, b n x ^ 2 ∂μ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, a x * b n x ∂μ) atTop (𝓝 0) := by
  have hb' : Tendsto (fun n => Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b n x ^ 2 ∂μ))
      atTop (𝓝 0) := by
    have := h.const_mul (Real.sqrt (∫ x, a x ^ 2 ∂μ))
    rwa [mul_zero] at this
  refine (tendsto_zero_iff_abs_tendsto_zero _).mpr (squeeze_zero (fun n => abs_nonneg _)
    (fun n => abs_integral_mul_le_sqrt ha (hb n)) hb')

theorem memLp_mul_entry {Q : Measure (FieldPair d)} {g : FieldPair d → ℝ} (hg : MemLp g 2 Q)
    {K : ℝ} (hgood : ∀ᵐ w ∂Q, ∀ x j k, |w.1 x j k| ≤ K) (j k : Fin d) :
    MemLp (fun w => g w * w.1 0 j k) 2 Q := by
  have hentry : Measurable fun w : FieldPair d => w.1 0 j k :=
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
  refine (hg.const_mul K).of_le (hg.aestronglyMeasurable.mul hentry.aestronglyMeasurable) ?_
  filter_upwards [hgood] with w hw
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, mul_comm (|g w|)]
  have hK : 0 ≤ K := (abs_nonneg _).trans (hw 0 j k)
  rw [abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_right (hw 0 j k) (abs_nonneg _)

theorem tendsto_integral_mul_sum_entries {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {g : FieldPair d → ℝ} (hg : MemLp g 2 Q) {K : ℝ}
    (hgood : ∀ᵐ w ∂Q, ∀ x j k, |w.1 x j k| ≤ K) (k : Fin d) {Gs : ℕ → FieldPair d → Vec d}
    {G : FieldPair d → Vec d} (hGs : ∀ n j, MemLp (fun w => Gs n w j) 2 Q)
    (hG : ∀ j, MemLp (fun w => G w j) 2 Q)
    (hc : ∀ j, Tendsto (fun n => eLpNorm (fun w => Gs n w j - G w j) 2 Q) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ w, g w * ∑ j, w.1 0 j k * Gs n w j ∂Q) atTop
      (𝓝 (∫ w, g w * ∑ j, w.1 0 j k * G w j ∂Q)) := by
  have e : ∀ (H : FieldPair d → Vec d), (∀ j, MemLp (fun w => H w j) 2 Q) →
      ∫ w, g w * ∑ j, w.1 0 j k * H w j ∂Q = ∑ j, ∫ w, (g w * w.1 0 j k) * H w j ∂Q := by
    intro H hH
    have hint : ∀ j, Integrable (fun w => (g w * w.1 0 j k) * H w j) Q := fun j =>
      (memLp_mul_entry hg hgood j k).integrable_mul (hH j)
    rw [← integral_finset_sum _ fun j _ => hint j]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h := tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun j _ =>
    tendsto_integral_mul_of_eLpNorm_two (memLp_mul_entry hg hgood j k) (fun n => hGs n j) (hG j)
      (hc j)
  rw [e G hG]
  exact h.congr fun n => (e (Gs n) (hGs n)).symm

theorem memLp_of_sub_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g h : Ω → ℝ}
    (hgh : MemLp (fun w => g w - h w) 2 μ) (hh : MemLp h 2 μ) : MemLp g 2 μ := by
  convert hgh.add hh using 1
  funext w
  simp

/-- **The smoothed equation for `H¹` test functions**: `smoothed_equation`, with the test `F`
replaced by any `u ∈ L²` with weak horizontal gradient `G ∈ L²`. -/
theorem smoothed_equation_H1 (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {μ0 : ℝ} {ρ f : FieldPair d → ℝ}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q))
    (hfm : Measurable f) (hf : MemLp f 2 (Carriers.reducedReferenceLaw Q))
    (heq : ∀ G : FieldPair d → ℝ, IsHorizontalTest G →
      μ0 * (∫ w, ρ w * G w ∂(Carriers.reducedReferenceLaw Q)) -
        ∫ w, ρ w * envGenerator hd lam G w ∂(Carriers.reducedReferenceLaw Q) =
          ∫ w, f w * G w ∂(Carriers.reducedReferenceLaw Q))
    {K : ℝ} {L : ℝ≥0}
    (hgood : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), (∀ x j k, |w.1 x j k| ≤ K) ∧
      ∀ j k, LipschitzWith L fun y => w.1 y j k)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {u : FieldPair d → ℝ} {G : FieldPair d → Vec d}
    (hum : Measurable u) (hu : MemLp u 2 (Carriers.reducedReferenceLaw Q)) (hGm : Measurable G)
    (hG : ∀ j, MemLp (fun w => G w j) 2 (Carriers.reducedReferenceLaw Q))
    (huG : HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ u G) :
    μ0 * (∫ w, smoothDensity d δ ρ w * u w ∂(Carriers.reducedReferenceLaw Q)) +
        (1 / 2 : ℝ) * ∑ k, (∫ w, smoothGrad d δ ρ w k * ∑ j, w.1 0 j k * G w j
          ∂(Carriers.reducedReferenceLaw Q)) -
        lam * (∫ w, smoothDensity d δ ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * G w j
          ∂(Carriers.reducedReferenceLaw Q)) -
        (∫ w, ρ w * commOp hd lam (Calculus.unitMassScaledMollifier d δ) G w
          ∂(Carriers.reducedReferenceLaw Q)) =
      ∫ w, smoothDensity d δ f w * u w ∂(Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  set κ := Calculus.unitMassScaledMollifier d δ with hκdef
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨F, Gs, hF, hGsm, hD, hFu, hFuc, hGu, hGuc⟩ :=
    exists_test_approximation hQ (q := 2) ENNReal.ofNat_ne_top huG hu hG hum hGm
  have hF2 : ∀ n, MemLp (F n) 2 μ := fun n => memLp_of_sub_add (hFu n) hu
  have hGs2 : ∀ n j, MemLp (fun w => Gs n w j) 2 μ := fun n j => memLp_of_sub_add (hGu n j) (hG j)
  have hK : ∀ᵐ w ∂μ, ∀ x j k, |w.1 x j k| ≤ K := hgood.mono fun w hw => hw.1
  have hLip : ∀ᵐ w ∂μ, ∀ j k, LipschitzWith L fun y => w.1 y j k := hgood.mono fun w hw => hw.2
  have hρδ := memLp_smoothDensity hQ hρm hρ hδ
  have hfδ := memLp_smoothDensity hQ hfm hf hδ
  have hgr := memLp_smoothGrad hQ hρm hρ hδ
  -- The equation along the approximating tests.
  have hn : ∀ n, μ0 * (∫ w, smoothDensity d δ ρ w * F n w ∂μ) +
        (1 / 2 : ℝ) * ∑ k, (∫ w, smoothGrad d δ ρ w k * ∑ j, w.1 0 j k * Gs n w j ∂μ) -
        lam * (∫ w, smoothDensity d δ ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * Gs n w j
          ∂μ) - (∫ w, ρ w * commOp hd lam κ (Gs n) w ∂μ) =
      ∫ w, smoothDensity d δ f w * F n w ∂μ := by
    intro n
    have h := smoothed_equation hd lam Q hQ hρm hρ hfm hf heq hgood hδ (hF n)
    have hDm : Measurable fun w j => horizontalDerivative j (F n) w :=
      Measurable.of_eval fun j => (hF n).measurable_derivative j
    have e2 : ∀ k, ∫ w, smoothGrad d δ ρ w k * testFlux (F n) w k ∂μ =
        ∫ w, smoothGrad d δ ρ w k * ∑ j, w.1 0 j k * Gs n w j ∂μ := fun k =>
      integral_congr_ae ((hD n).mono fun w hw => by
        simp only [testFlux, hw])
    have e3 : ∫ w, smoothDensity d δ ρ w * testDrift hd (F n) w ∂μ =
        ∫ w, smoothDensity d δ ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * Gs n w j ∂μ :=
      integral_congr_ae ((hD n).mono fun w hw => by
        simp only [testDrift, hw])
    have e4 : ∫ w, ρ w * commOp hd lam κ (fun w' j => horizontalDerivative j (F n) w') w ∂μ =
        ∫ w, ρ w * commOp hd lam κ (Gs n) w ∂μ :=
      integral_congr_ae ((commOp_congr_ae hd lam hQ κ hDm (hGsm n) (hD n)).mono fun w hw => by
        simp only [hw])
    rw [Finset.sum_congr rfl fun k _ => e2 k, e3, e4] at h
    exact h
  -- Each term converges.
  have t1 : Tendsto (fun n => ∫ w, smoothDensity d δ ρ w * F n w ∂μ) atTop
      (𝓝 (∫ w, smoothDensity d δ ρ w * u w ∂μ)) :=
    tendsto_integral_mul_of_eLpNorm_two hρδ hF2 hu hFuc
  have t5 : Tendsto (fun n => ∫ w, smoothDensity d δ f w * F n w ∂μ) atTop
      (𝓝 (∫ w, smoothDensity d δ f w * u w ∂μ)) :=
    tendsto_integral_mul_of_eLpNorm_two hfδ hF2 hu hFuc
  have t2 : ∀ k, Tendsto (fun n => ∫ w, smoothGrad d δ ρ w k * ∑ j, w.1 0 j k * Gs n w j ∂μ)
      atTop (𝓝 (∫ w, smoothGrad d δ ρ w k * ∑ j, w.1 0 j k * G w j ∂μ)) := fun k =>
    tendsto_integral_mul_sum_entries (hgr k) hK k hGs2 hG hGuc
  have t3 : Tendsto (fun n => ∫ w, smoothDensity d δ ρ w *
        ∑ j, w.1 0 j (firstCoordinateIndex hd) * Gs n w j ∂μ) atTop
      (𝓝 (∫ w, smoothDensity d δ ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * G w j ∂μ)) :=
    tendsto_integral_mul_sum_entries hρδ hK _ hGs2 hG hGuc
  have t4 : Tendsto (fun n => ∫ w, ρ w * commOp hd lam κ (Gs n) w ∂μ) atTop
      (𝓝 (∫ w, ρ w * commOp hd lam κ G w ∂μ)) := by
    have hdm : ∀ n, Measurable fun w j => Gs n w j - G w j := fun n =>
      Measurable.of_eval fun j =>
        ((measurable_pi_apply j).comp (hGsm n)).sub ((measurable_pi_apply j).comp hGm)
    have hdiff : ∀ n, ∫ w, ρ w * commOp hd lam κ (Gs n) w ∂μ - ∫ w, ρ w * commOp hd lam κ G w ∂μ =
        ∫ w, ρ w * commOp hd lam κ (fun w' j => Gs n w' j - G w' j) w ∂μ := fun n => by
      have hi1 : Integrable (fun w => ρ w * commOp hd lam κ (Gs n) w) μ :=
        hρ.integrable_mul (memLp_commOp hd lam hQ hδ hLip (hGsm n) (hGs2 n))
      have hi2 : Integrable (fun w => ρ w * commOp hd lam κ G w) μ :=
        hρ.integrable_mul (memLp_commOp hd lam hQ hδ hLip hGm hG)
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae ((commOp_sub_ae hd lam hQ hδ hLip (hGsm n) hGm (hGs2 n) hG).mono
        fun w hw => ?_)
      beta_reduce
      rw [← mul_sub]
      exact congrArg (fun t => ρ w * t) hw.symm
    have hsq : ∀ j, Tendsto (fun n => Real.sqrt (∫ w, (Gs n w j - G w j) ^ 2 ∂μ)) atTop (𝓝 0) :=
      fun j => tendsto_sqrt_integral_sq (fun n => hGu n j) (hGuc j)
    have hbd : Tendsto (fun n => commConst d lam L * Real.sqrt (∫ w, ρ w ^ 2 ∂μ) *
        ∑ j, Real.sqrt (∫ w, (Gs n w j - G w j) ^ 2 ∂μ)) atTop (𝓝 0) := by
      have := (tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun j _ => hsq j).const_mul
        (commConst d lam L * Real.sqrt (∫ w, ρ w ^ 2 ∂μ))
      simpa using this
    have hz : Tendsto (fun n => ∫ w, ρ w * commOp hd lam κ (Gs n) w ∂μ -
        ∫ w, ρ w * commOp hd lam κ G w ∂μ) atTop (𝓝 0) := by
      refine (tendsto_zero_iff_abs_tendsto_zero _).mpr (squeeze_zero (fun n => abs_nonneg _)
        (fun n => ?_) hbd)
      rw [Function.comp_apply, hdiff n]
      exact abs_integral_mul_commOp_le hd lam hQ hδ hδ1 hLip hρm hρ (hdm n) fun j => hGu n j
    have := hz.add_const (∫ w, ρ w * commOp hd lam κ G w ∂μ)
    simpa using this
  have hlim := ((((t1.const_mul μ0).add ((tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun k _ => t2 k).const_mul
    (1 / 2 : ℝ))).sub (t3.const_mul lam)).sub t4)
  exact tendsto_nhds_unique (hlim.congr fun n => hn n) t5

/-! ## The energy estimate -/

theorem sourceReducedBound_pos' (L : ℝ) : 0 < sourceReducedBound L := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg (6 * L + 1)])

theorem commConst_nonneg (d : ℕ) (lam : ℝ) (L : ℝ≥0) : 0 ≤ commConst d lam L := by
  unfold commConst
  exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => add_nonneg
    (mul_nonneg L.coe_nonneg (norm_nonneg _))
    (mul_nonneg L.coe_nonneg (integral_nonneg fun u => abs_nonneg _))))
    (mul_nonneg (abs_nonneg _) L.coe_nonneg)

theorem integral_sq_smoothDensity_le {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ρ : FieldPair d → ℝ} (hρm : Measurable ρ) (hρ : MemLp ρ 2 Q)
    {δ : ℝ} (hδ : 0 < δ) : ∫ w, smoothDensity d δ ρ w ^ 2 ∂Q ≤ ∫ w, ρ w ^ 2 ∂Q := by
  have hs := contDiff_reflectKernel (contDiff_unitMassScaledMollifier (d := d) δ)
  have h := (integral_sq_horizontalMollify_le hQ
    (k := reflectKernel (Calculus.unitMassScaledMollifier d δ))
    (fun x => unitMassScaledMollifier_nonneg' hδ (-x)) hs.continuous.measurable
    (hs.continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_reflectKernel (hasCompactSupport_unitMassScaledMollifier hδ))) hρm hρ).2
  have h1 : ∫ x, reflectKernel (Calculus.unitMassScaledMollifier d δ) x = 1 := by
    unfold reflectKernel
    rw [integral_neg_eq_self (fun x => Calculus.unitMassScaledMollifier d δ x)]
    exact integral_unitMassScaledMollifier' hδ
  rw [h1, one_pow, one_mul] at h
  exact h

/-- **The energy estimate**: `‖Dρ^δ‖₂²` is bounded uniformly in `δ ∈ (0, 1]`. -/
theorem energy_bound (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {μ0 : ℝ} {ρ f : FieldPair d → ℝ}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q))
    (hfm : Measurable f) (hf : MemLp f 2 (Carriers.reducedReferenceLaw Q))
    (heq : ∀ G : FieldPair d → ℝ, IsHorizontalTest G →
      μ0 * (∫ w, ρ w * G w ∂(Carriers.reducedReferenceLaw Q)) -
        ∫ w, ρ w * envGenerator hd lam G w ∂(Carriers.reducedReferenceLaw Q) =
          ∫ w, f w * G w ∂(Carriers.reducedReferenceLaw Q))
    {K : ℝ} {L : ℝ≥0}
    (hgood : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), (∀ x j k, |w.1 x j k| ≤ K) ∧
      ∀ j k, LipschitzWith L fun y => w.1 y j k)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∑ k, ∫ w, smoothGrad d δ ρ w k ^ 2 ∂(Carriers.reducedReferenceLaw Q) ≤
      4 * sourceReducedBound Λ₀ *
          (Real.sqrt (∫ w, f w ^ 2 ∂(Carriers.reducedReferenceLaw Q)) *
              Real.sqrt (∫ w, ρ w ^ 2 ∂(Carriers.reducedReferenceLaw Q)) +
            |μ0| * ∫ w, ρ w ^ 2 ∂(Carriers.reducedReferenceLaw Q)) +
        (2 * sourceReducedBound Λ₀ * d * (|lam| * K + commConst d lam L) *
          Real.sqrt (∫ w, ρ w ^ 2 ∂(Carriers.reducedReferenceLaw Q))) ^ 2 := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  have hr := memLp_smoothDensity hQ hρm hρ hδ
  have hrm := measurable_smoothDensity hρm δ
  have hgm := measurable_smoothGrad hρm hδ
  have hg := memLp_smoothGrad hQ hρm hρ hδ
  have h := smoothed_equation_H1 hd lam Q hQ hρm hρ hfm hf heq hgood hδ hδ1 hrm hr hgm hg
    (hasWeakHorizontalGradient_smoothDensity hQ hρm hρ hδ)
  have hell := ae_reduced_elliptic_zero Q
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  set Λ := sourceReducedBound Λ₀ with hΛdef
  have hΛ : 0 < Λ := sourceReducedBound_pos' Λ₀
  set g := smoothGrad d δ ρ with hgdef
  set r := smoothDensity d δ ρ with hrdef
  set R := Real.sqrt (∫ w, ρ w ^ 2 ∂μ) with hRdef
  set Rf := Real.sqrt (∫ w, f w ^ 2 ∂μ) with hRfdef
  set E := ∑ k, ∫ w, g w k ^ 2 ∂μ with hEdef
  set X := ∑ j, Real.sqrt (∫ w, g w j ^ 2 ∂μ) with hXdef
  set cC := commConst d lam L with hcCdef
  have hK : ∀ᵐ w ∂μ, ∀ x j k, |w.1 x j k| ≤ K := hgood.mono fun w hw => hw.1
  have hLip : ∀ᵐ w ∂μ, ∀ j k, LipschitzWith L fun y => w.1 y j k := hgood.mono fun w hw => hw.2
  have hK0 : 0 ≤ K := by
    obtain ⟨w, hw⟩ := hK.exists
    exact (abs_nonneg _).trans (hw 0 ⟨0, by omega⟩ ⟨0, by omega⟩)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun k _ => integral_nonneg fun w => sq_nonneg _
  have hX : X ≤ d * Real.sqrt E := by
    calc X ≤ ∑ j : Fin d, Real.sqrt E := Finset.sum_le_sum fun j _ => Real.sqrt_le_sqrt
          (Finset.single_le_sum (f := fun k => ∫ w, g w k ^ 2 ∂μ)
            (fun k _ => integral_nonneg fun w => sq_nonneg _) (Finset.mem_univ j))
      _ = d * Real.sqrt E := by simp
  have hrr : ∫ w, r w ^ 2 ∂μ ≤ ∫ w, ρ w ^ 2 ∂μ := integral_sq_smoothDensity_le hQ hρm hρ hδ
  have hrR : Real.sqrt (∫ w, r w ^ 2 ∂μ) ≤ R := Real.sqrt_le_sqrt hrr
  have hfδR : Real.sqrt (∫ w, smoothDensity d δ f w ^ 2 ∂μ) ≤ Rf :=
    Real.sqrt_le_sqrt (integral_sq_smoothDensity_le hQ hfm hf hδ)
  -- The four terms.
  have hT1 : |∫ w, smoothDensity d δ f w * r w ∂μ| ≤ Rf * R :=
    (abs_integral_mul_le_sqrt (memLp_smoothDensity hQ hfm hf hδ) hr).trans
      (mul_le_mul hfδR hrR (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hT2 : |μ0 * ∫ w, r w * r w ∂μ| ≤ |μ0| * ∫ w, ρ w ^ 2 ∂μ := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have e : ∫ w, r w * r w ∂μ = ∫ w, r w ^ 2 ∂μ :=
      integral_congr_ae (ae_of_all _ fun w => (sq _).symm)
    rw [e, abs_of_nonneg (integral_nonneg fun w => sq_nonneg _)]
    exact hrr
  have hT3 : |∫ w, r w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * g w j ∂μ| ≤ K * (R * X) := by
    have hint : ∀ j, Integrable (fun w => |r w| * |g w j|) μ := fun j =>
      hr.abs.integrable_mul (hg j).abs
    have hj : ∀ j, ∫ w, |r w| * |g w j| ∂μ ≤ R * Real.sqrt (∫ w, g w j ^ 2 ∂μ) := fun j => by
      have h1 := abs_integral_mul_le_sqrt (f := fun w => |r w|) (g := fun w => |g w j|)
        hr.abs (hg j).abs
      simp only [sq_abs] at h1
      exact (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right hrR (Real.sqrt_nonneg _)))
    calc |∫ w, r w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * g w j ∂μ|
        ≤ ∫ w, |r w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * g w j| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ w, K * ∑ j, |r w| * |g w j| ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _)
          ((integrable_finset_sum _ fun j _ => hint j).const_mul K) ?_
        filter_upwards [hK] with w hw
        rw [abs_mul]
        calc |r w| * |∑ j, w.1 0 j (firstCoordinateIndex hd) * g w j|
            ≤ |r w| * ∑ j, |w.1 0 j (firstCoordinateIndex hd) * g w j| :=
              mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
          _ ≤ |r w| * ∑ j, K * |g w j| := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (abs_nonneg _)
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (hw 0 j _) (abs_nonneg _)
          _ = K * ∑ j, |r w| * |g w j| := by
              rw [Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
      _ = K * ∑ j, ∫ w, |r w| * |g w j| ∂μ := by
        rw [integral_const_mul, integral_finset_sum _ fun j _ => hint j]
      _ ≤ K * ∑ j, R * Real.sqrt (∫ w, g w j ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hj j) hK0
      _ = K * (R * X) := by rw [← Finset.mul_sum]
  have hT3' : |lam * ∫ w, r w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * g w j ∂μ| ≤
      |lam| * (K * (R * X)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hT3 (abs_nonneg _)
  have hT4 : |∫ w, ρ w * commOp hd lam (Calculus.unitMassScaledMollifier d δ) g w ∂μ| ≤
      cC * R * X :=
    abs_integral_mul_commOp_le hd lam hQ hδ hδ1 hLip hρm hρ hgm hg
  -- Ellipticity.
  have hS : Λ⁻¹ * E ≤ ∑ k, ∫ w, g w k * ∑ j, w.1 0 j k * g w j ∂μ := by
    have hint : ∀ k, Integrable (fun w => g w k * ∑ j, w.1 0 j k * g w j) μ := fun k =>
      (hg k).integrable_mul (memLp_finset_sum _ fun j _ => by
        simpa only [mul_comm] using memLp_mul_entry (hg j) hK j k)
    have hint2 : ∀ k, Integrable (fun w => g w k ^ 2) μ := fun k =>
      (memLp_two_iff_integrable_sq (hg k).aestronglyMeasurable).mp (hg k)
    rw [← integral_finset_sum _ fun k _ => hint k, hEdef,
      ← integral_finset_sum _ fun k _ => hint2 k, ← integral_const_mul]
    refine integral_mono_ae ((integrable_finset_sum _ fun k _ => hint2 k).const_mul _)
      (integrable_finset_sum _ fun k _ => hint k) ?_
    filter_upwards [hell] with w hw
    obtain ⟨hsym, hellw⟩ := hw
    have h1 := (hellw (g w)).1
    have e1 : euclideanSq (g w) = ∑ k, g w k ^ 2 := by
      unfold euclideanSq dot
      exact Finset.sum_congr rfl fun k _ => (sq _).symm
    have e2 : dot (g w) ((w.1 0).mulVec (g w)) = ∑ k, g w k * ∑ j, w.1 0 j k * g w j := by
      unfold dot
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      have := congrFun (congrFun hsym k) j
      rw [Matrix.transpose_apply] at this
      exact this.symm
    rw [e1, e2] at h1
    exact h1
  -- Assembly.
  have hS2 : ∑ k, ∫ w, g w k * ∑ j, w.1 0 j k * g w j ∂μ ≤
      2 * (Rf * R + |μ0| * ∫ w, ρ w ^ 2 ∂μ + (|lam| * K + cC) * R * X) := by
    have a1 := le_abs_self (∫ w, smoothDensity d δ f w * r w ∂μ)
    have a2 := neg_abs_le (μ0 * ∫ w, r w * r w ∂μ)
    have a3 := le_abs_self (lam * ∫ w, r w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * g w j ∂μ)
    have a4 := le_abs_self
      (∫ w, ρ w * commOp hd lam (Calculus.unitMassScaledMollifier d δ) g w ∂μ)
    nlinarith
  have hE1 : E ≤ Λ * (2 * (Rf * R + |μ0| * ∫ w, ρ w ^ 2 ∂μ + (|lam| * K + cC) * R * X)) := by
    have := mul_le_mul_of_nonneg_left (hS.trans hS2) hΛ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul] at this
  have hB0 : 0 ≤ (|lam| * K + cC) * R :=
    mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hK0) (commConst_nonneg d lam L)) hR0
  have hX' : 2 * Λ * ((|lam| * K + cC) * R * X) ≤
      2 * Λ * ((|lam| * K + cC) * R * (d * Real.sqrt E)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hB0) (by positivity)
  have ht : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE0
  nlinarith [sq_nonneg (Real.sqrt E - 2 * Λ * d * ((|lam| * K + cC) * R)), Real.sqrt_nonneg E]

/-! ## Weak limits and the weak gradient of the density -/

/-- A bounded sequence in a Hilbert space whose pairings converge on a dense set has a weak
limit (Banach–Steinhaus and the Riesz representation). -/
theorem exists_weak_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {D : Set E} (hD : Dense D) {v : ℕ → E} {A : ℝ} (hA : ∀ n, ‖v n‖ ≤ A)
    (hconv : ∀ s ∈ D, ∃ c, Tendsto (fun n => inner ℝ (v n) s) atTop (𝓝 c)) :
    ∃ v0 : E, ∀ h, Tendsto (fun n => inner ℝ (v n) h) atTop (𝓝 (inner ℝ v0 h)) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hcauchy : ∀ h : E, CauchySeq fun n => inner ℝ (v n) h := by
    intro h
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hη : 0 < ε / (3 * (A + 1)) := by positivity
    obtain ⟨s, hs, hhs⟩ := hD.exists_dist_lt h hη
    obtain ⟨c, hc⟩ := hconv s hs
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc.cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : ∀ k, |inner ℝ (v k) h - inner ℝ (v k) s| ≤ A * (ε / (3 * (A + 1))) := fun k => by
      rw [← inner_sub_right]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [← dist_eq_norm]
      exact mul_le_mul (hA k) hhs.le dist_nonneg hA0
    have hAη : A * (ε / (3 * (A + 1))) < ε / 3 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h1 := hN m hm n hn
    rw [Real.dist_eq] at h1 ⊢
    have hbm := abs_le.mp (hb m)
    have hbn := abs_le.mp (hb n)
    have h1' := abs_lt.mp h1
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  choose f hf using fun h => cauchySeq_tendsto_of_complete (hcauchy h)
  have hT : Tendsto (fun n x => innerSL ℝ (v n) x) atTop (𝓝 f) :=
    tendsto_pi_nhds.mpr fun x => by simpa only [innerSL_apply_apply] using hf x
  refine ⟨(InnerProductSpace.toDual ℝ E).symm
    (continuousLinearMapOfTendsto (fun n => innerSL ℝ (v n)) hT), fun h => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hf h

theorem inner_Lp_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Lp ℝ 2 μ)
    {g : Ω → ℝ} (hg : MemLp g 2 μ) : inner ℝ f (hg.toLp g) = ∫ w, f w * g w ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with w hw
  rw [hw, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The `L²` form: a bounded sequence whose pairings with horizontal tests converge has a weak
limit in `L²`. -/
theorem exists_weak_limit_Lp {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : ℕ → FieldPair d → ℝ} (hu : ∀ n, MemLp (u n) 2 Q) {A : ℝ}
    (hA : ∀ n, ∫ w, u n w ^ 2 ∂Q ≤ A)
    (hconv : ∀ F, IsHorizontalTest F →
      ∃ c, Tendsto (fun n => ∫ w, u n w * F w ∂Q) atTop (𝓝 c)) :
    ∃ V : FieldPair d → ℝ, Measurable V ∧ MemLp V 2 Q ∧ ∀ h : FieldPair d → ℝ, MemLp h 2 Q →
      Tendsto (fun n => ∫ w, u n w * h w ∂Q) atTop (𝓝 (∫ w, V w * h w ∂Q)) := by
  have e : ∀ n {h : FieldPair d → ℝ} (hh : MemLp h 2 Q),
      inner ℝ ((hu n).toLp (u n)) (hh.toLp h) = ∫ w, u n w * h w ∂Q := fun n h hh => by
    rw [inner_Lp_toLp]
    refine integral_congr_ae ?_
    filter_upwards [(hu n).coeFn_toLp] with w hw
    rw [hw]
  have hD : Dense {v : Lp ℝ 2 Q | ∃ F : FieldPair d → ℝ, IsHorizontalTest F ∧
      ∃ hF : MemLp F 2 Q, hF.toLp F = v} :=
    dense_iff_closure_eq.mpr (Correctors.closure_horizontalCore_Lp_eq_univ Q hQ)
  have hnorm : ∀ n, ‖(hu n).toLp (u n)‖ ≤ Real.sqrt A := fun n => by
    have h1 := real_inner_self_eq_norm_sq ((hu n).toLp (u n))
    rw [e n (hu n)] at h1
    have h2 : ∫ w, u n w * u n w ∂Q ≤ A := by
      have := hA n
      simpa only [sq] using this
    rw [← Real.sqrt_sq (norm_nonneg _), ← h1]
    exact Real.sqrt_le_sqrt h2
  obtain ⟨v0, hv0⟩ := exists_weak_limit hD hnorm (fun s hs => by
    obtain ⟨F, hF, hF2, rfl⟩ := hs
    obtain ⟨c, hc⟩ := hconv F hF
    exact ⟨c, hc.congr fun n => (e n hF2).symm⟩)
  refine ⟨⇑v0, (Lp.stronglyMeasurable v0).measurable, Lp.memLp v0, fun h hh => ?_⟩
  have := hv0 (hh.toLp h)
  rw [inner_Lp_toLp] at this
  exact this.congr fun n => e n hh

theorem reflectKernel_unitMassScaledMollifier (δ : ℝ) :
    reflectKernel (Calculus.unitMassScaledMollifier d δ) = Calculus.unitMassScaledMollifier d δ := by
  funext x
  unfold reflectKernel Calculus.unitMassScaledMollifier
  rw [smul_neg]
  unfold mollifier
  rw [ContDiffBump.normed_neg]

theorem smoothDensity_eq (δ : ℝ) (ρ : FieldPair d → ℝ) :
    smoothDensity d δ ρ = horizontalMollify (Calculus.unitMassScaledMollifier d δ) ρ := by
  unfold smoothDensity
  rw [reflectKernel_unitMassScaledMollifier]

theorem tendsto_eLpNorm_smoothDensity {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ρ : FieldPair d → ℝ} (hρm : Measurable ρ) (hρ : MemLp ρ 2 Q) :
    Tendsto (fun n => eLpNorm (fun w => smoothDensity d (scaleSeq n) ρ w - ρ w) 2 Q) atTop
      (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  simp only [smoothDensity_eq]
  exact tendsto_eLpNorm_mollify_scaleSeq hQ ENNReal.ofNat_ne_top hρm hρ

/-- **The density has a weak gradient in `L²`**: the weak limit of `Dρ^δ` along `δ = scaleSeq n`. -/
theorem exists_weak_gradient (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {μ0 : ℝ} {ρ f : FieldPair d → ℝ}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q))
    (hfm : Measurable f) (hf : MemLp f 2 (Carriers.reducedReferenceLaw Q))
    (heq : ∀ G : FieldPair d → ℝ, IsHorizontalTest G →
      μ0 * (∫ w, ρ w * G w ∂(Carriers.reducedReferenceLaw Q)) -
        ∫ w, ρ w * envGenerator hd lam G w ∂(Carriers.reducedReferenceLaw Q) =
          ∫ w, f w * G w ∂(Carriers.reducedReferenceLaw Q))
    {K : ℝ} {L : ℝ≥0}
    (hgood : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), (∀ x j k, |w.1 x j k| ≤ K) ∧
      ∀ j k, LipschitzWith L fun y => w.1 y j k) :
    ∃ V : FieldPair d → Vec d, Measurable V ∧
      (∀ j, MemLp (fun w => V w j) 2 (Carriers.reducedReferenceLaw Q)) ∧
      HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ ρ V := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ∑ k, ∫ w, smoothGrad d (scaleSeq n) ρ w k ^ 2
      ∂(Carriers.reducedReferenceLaw Q) ≤ C :=
    ⟨_, fun n => energy_bound hd lam Q hQ hρm hρ hfm hf heq hgood (scaleSeq_pos n)
      (scaleSeq_le_one n)⟩
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  have hA : ∀ i n, ∫ w, smoothGrad d (scaleSeq n) ρ w i ^ 2 ∂μ ≤ C := fun i n =>
    (Finset.single_le_sum (f := fun k => ∫ w, smoothGrad d (scaleSeq n) ρ w k ^ 2 ∂μ)
      (fun k _ => integral_nonneg fun w => sq_nonneg _) (Finset.mem_univ i)).trans (hC n)
  have hlimρ : ∀ i (K : FieldPair d → ℝ), IsHorizontalTest K →
      Tendsto (fun n => ∫ w, smoothDensity d (scaleSeq n) ρ w * horizontalDerivative i K w ∂μ)
        atTop (𝓝 (∫ w, ρ w * horizontalDerivative i K w ∂μ)) := by
    intro i K hK
    have hDK2 : MemLp (horizontalDerivative i K) 2 μ := hK.memLp_derivative μ 2 i
    have h := tendsto_integral_mul_of_eLpNorm_two hDK2
      (fun n => memLp_smoothDensity hQ hρm hρ (scaleSeq_pos n)) hρ
      (tendsto_eLpNorm_smoothDensity hQ hρm hρ)
    have e1 : ∀ n, ∫ w, horizontalDerivative i K w * smoothDensity d (scaleSeq n) ρ w ∂μ =
        ∫ w, smoothDensity d (scaleSeq n) ρ w * horizontalDerivative i K w ∂μ := fun n =>
      integral_congr_ae (ae_of_all _ fun w => mul_comm _ _)
    have e2 : ∫ w, horizontalDerivative i K w * ρ w ∂μ =
        ∫ w, ρ w * horizontalDerivative i K w ∂μ :=
      integral_congr_ae (ae_of_all _ fun w => mul_comm _ _)
    rw [e2] at h
    exact h.congr e1
  have hV : ∀ i, ∃ Vi : FieldPair d → ℝ, Measurable Vi ∧ MemLp Vi 2 μ ∧
      ∀ h : FieldPair d → ℝ, MemLp h 2 μ →
        Tendsto (fun n => ∫ w, smoothGrad d (scaleSeq n) ρ w i * h w ∂μ) atTop
          (𝓝 (∫ w, Vi w * h w ∂μ)) := fun i =>
    exists_weak_limit_Lp hQ (u := fun n w => smoothGrad d (scaleSeq n) ρ w i)
      (fun n => memLp_smoothGrad hQ hρm hρ (scaleSeq_pos n) i) (hA i) fun F hF =>
        ⟨-(∫ w, ρ w * horizontalDerivative i F w ∂μ), by
          refine (hlimρ i F hF).neg.congr fun n => ?_
          beta_reduce
          rw [integral_smoothDensity_mul_derivative hQ hρm hρ (scaleSeq_pos n) i hF, neg_neg]⟩
  choose V hVm hV2 hVlim using hV
  refine ⟨fun w i => V i w, Measurable.of_eval hVm, hV2, ?_⟩
  refine hasWeakHorizontalGradient_of_tests hQ hρm hρ (Measurable.of_eval hVm) hV2
    fun i K hK => ?_
  obtain ⟨B, -, hB⟩ := hK.bound_orbit
  have hK2 : MemLp K 2 μ := memLp_of_ae_bound' hK.1 (ae_of_all _ fun ω => by simpa using hB ω 0) 2
  have h3 : Tendsto (fun n => ∫ w, smoothDensity d (scaleSeq n) ρ w * horizontalDerivative i K w
      ∂μ) atTop (𝓝 (-(∫ w, V i w * K w ∂μ))) :=
    (hVlim i K hK2).neg.congr fun n =>
      (integral_smoothDensity_mul_derivative hQ hρm hρ (scaleSeq_pos n) i hK).symm
  exact tendsto_nhds_unique (hlimρ i K hK) h3

/-! ## The `H¹` weak form for the density -/

/-- Duality between a weak gradient and a weak divergence: `E[W·Du] = -E[h u]`. -/
theorem sum_integral_mul_eq_neg_of_div {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} {V : FieldPair d → Vec d} (hum : Measurable u)
    (hu : MemLp u 2 Q) (hVm : Measurable V) (hV : ∀ k, MemLp (fun w => V w k) 2 Q)
    (huV : HasWeakHorizontalGradient Q hQ u V) {W : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    (hW : HasWeakHorizontalDivergence Q hQ W h) (hW2 : ∀ k, MemLp (fun w => W w k) 2 Q)
    (hh : MemLp h 2 Q) :
    ∑ k, ∫ w, W w k * V w k ∂Q = -∫ w, h w * u w ∂Q := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨F, Gs, hF, hGsm, hD, hFu, hFuc, hGu, hGuc⟩ :=
    exists_test_approximation hQ (q := 2) ENNReal.ofNat_ne_top huV hu hV hum hVm
  have hF2 : ∀ n, MemLp (F n) 2 Q := fun n => memLp_of_sub_add (hFu n) hu
  have hGs2 : ∀ n k, MemLp (fun w => Gs n w k) 2 Q := fun n k => memLp_of_sub_add (hGu n k) (hV k)
  have hn : ∀ n, ∑ k, ∫ w, W w k * Gs n w k ∂Q = -∫ w, h w * F n w ∂Q := fun n => by
    have hint : ∀ k, Integrable (fun w => W w k * Gs n w k) Q := fun k =>
      (hW2 k).integrable_mul (hGs2 n k)
    rw [← HasWeakHorizontalDivergence.integral_test hW (hF n),
      ← integral_finset_sum _ fun k _ => hint k]
    refine integral_congr_ae ((hD n).mono fun w hw => ?_)
    simp only [hw]
  have t1 : Tendsto (fun n => ∑ k, ∫ w, W w k * Gs n w k ∂Q) atTop
      (𝓝 (∑ k, ∫ w, W w k * V w k ∂Q)) :=
    tendsto_finset_sum _ fun k _ =>
      tendsto_integral_mul_of_eLpNorm_two (hW2 k) (fun n => hGs2 n k) (hV k) (hGuc k)
  have t2 : Tendsto (fun n => -∫ w, h w * F n w ∂Q) atTop (𝓝 (-∫ w, h w * u w ∂Q)) :=
    (tendsto_integral_mul_of_eLpNorm_two hh hF2 hu hFuc).neg
  exact tendsto_nhds_unique (t1.congr hn) t2

theorem memLp_entry_sum {Q : Measure (FieldPair d)} {K : ℝ}
    (hK : ∀ᵐ w ∂Q, ∀ x j k, |w.1 x j k| ≤ K) {G : FieldPair d → Vec d}
    (hG : ∀ j, MemLp (fun w => G w j) 2 Q) (k : Fin d) :
    MemLp (fun w => ∑ j, w.1 0 j k * G w j) 2 Q :=
  memLp_finset_sum _ fun j _ => by simpa only [mul_comm] using memLp_mul_entry (hG j) hK j k

/-- The weak form against horizontal tests, once `ρ` has a weak gradient `V ∈ L²`. -/
theorem weak_form_tests (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {μ0 : ℝ} {ρ f : FieldPair d → ℝ}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q))
    (heq : ∀ G : FieldPair d → ℝ, IsHorizontalTest G →
      μ0 * (∫ w, ρ w * G w ∂(Carriers.reducedReferenceLaw Q)) -
        ∫ w, ρ w * envGenerator hd lam G w ∂(Carriers.reducedReferenceLaw Q) =
          ∫ w, f w * G w ∂(Carriers.reducedReferenceLaw Q))
    {K : ℝ} (hK : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), ∀ x j k, |w.1 x j k| ≤ K)
    {V : FieldPair d → Vec d} (hVm : Measurable V)
    (hV : ∀ j, MemLp (fun w => V w j) 2 (Carriers.reducedReferenceLaw Q))
    (hρV : HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ ρ V)
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    μ0 * (∫ w, ρ w * F w ∂(Carriers.reducedReferenceLaw Q)) +
        (1 / 2 : ℝ) * ∑ k, (∫ w, V w k * ∑ j, w.1 0 j k * horizontalDerivative j F w
          ∂(Carriers.reducedReferenceLaw Q)) -
        lam * (∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j F w
          ∂(Carriers.reducedReferenceLaw Q)) =
      ∫ w, f w * F w ∂(Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  have h := heq F hF
  have hdiv := hasWeakHorizontalDivergence_testFlux Q hQ hF
  have hTFD := memLp_testFluxDiv Q hQ hF 2
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  have hDF : ∀ j, MemLp (fun w => horizontalDerivative j F w) 2 μ := fun j =>
    hF.memLp_derivative μ 2 j
  have hTF : ∀ k, MemLp (fun w => testFlux F w k) 2 μ := fun k =>
    memLp_entry_sum hK (G := fun w j => horizontalDerivative j F w) hDF k
  have hTD : MemLp (fun w => ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j F w)
      2 μ := memLp_entry_sum hK (G := fun w j => horizontalDerivative j F w) hDF _
  have hdual := sum_integral_mul_eq_neg_of_div hQ hρm hρ hVm hV hρV hdiv hTF hTFD
  have e2 : ∀ k, ∫ w, testFlux F w k * V w k ∂μ =
      ∫ w, V w k * ∑ j, w.1 0 j k * horizontalDerivative j F w ∂μ := fun k =>
    integral_congr_ae (ae_of_all _ fun w => mul_comm _ _)
  rw [Finset.sum_congr rfl fun k _ => e2 k] at hdual
  have i1 : Integrable (fun w => (1 / 2 : ℝ) * (testFluxDiv F w * ρ w)) μ :=
    (hTFD.integrable_mul hρ).const_mul _
  have i2 : Integrable (fun w => lam *
      (ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j F w)) μ :=
    (hρ.integrable_mul hTD).const_mul _
  have e : ∀ w, ρ w * envGenerator hd lam F w = (1 / 2 : ℝ) * (testFluxDiv F w * ρ w) +
      lam * (ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j F w) :=
    fun w => by rw [envGenerator_eq_testFluxDiv]; ring
  have hsplit : ∫ w, ρ w * envGenerator hd lam F w ∂μ =
      (1 / 2 : ℝ) * ∫ w, testFluxDiv F w * ρ w ∂μ +
        lam * ∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j F w ∂μ := by
    rw [integral_congr_ae (ae_of_all _ e), integral_add i1 i2, integral_const_mul,
      integral_const_mul]
  linarith

/-- **The `H¹` weak form**: `μ E[ρu] + ½ E[V·aG] - λ E[ρ (ae₁)·G] = E[fu]` for every `u ∈ L²`
with weak gradient `G ∈ L²`. -/
theorem weak_form_H1 (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {μ0 : ℝ} {ρ f : FieldPair d → ℝ}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q))
    (hf : MemLp f 2 (Carriers.reducedReferenceLaw Q))
    (heq : ∀ G : FieldPair d → ℝ, IsHorizontalTest G →
      μ0 * (∫ w, ρ w * G w ∂(Carriers.reducedReferenceLaw Q)) -
        ∫ w, ρ w * envGenerator hd lam G w ∂(Carriers.reducedReferenceLaw Q) =
          ∫ w, f w * G w ∂(Carriers.reducedReferenceLaw Q))
    {K : ℝ} (hK : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), ∀ x j k, |w.1 x j k| ≤ K)
    {V : FieldPair d → Vec d} (hVm : Measurable V)
    (hV : ∀ j, MemLp (fun w => V w j) 2 (Carriers.reducedReferenceLaw Q))
    (hρV : HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ ρ V)
    {u : FieldPair d → ℝ} {G : FieldPair d → Vec d}
    (hum : Measurable u) (hu : MemLp u 2 (Carriers.reducedReferenceLaw Q)) (hGm : Measurable G)
    (hG : ∀ j, MemLp (fun w => G w j) 2 (Carriers.reducedReferenceLaw Q))
    (huG : HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ u G) :
    μ0 * (∫ w, ρ w * u w ∂(Carriers.reducedReferenceLaw Q)) +
        (1 / 2 : ℝ) * ∑ k, (∫ w, V w k * ∑ j, w.1 0 j k * G w j
          ∂(Carriers.reducedReferenceLaw Q)) -
        lam * (∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * G w j
          ∂(Carriers.reducedReferenceLaw Q)) =
      ∫ w, f w * u w ∂(Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨F, Gs, hF, hGsm, hD, hFu, hFuc, hGu, hGuc⟩ :=
    exists_test_approximation hQ (q := 2) ENNReal.ofNat_ne_top huG hu hG hum hGm
  have hF2 : ∀ n, MemLp (F n) 2 μ := fun n => memLp_of_sub_add (hFu n) hu
  have hGs2 : ∀ n j, MemLp (fun w => Gs n w j) 2 μ := fun n j => memLp_of_sub_add (hGu n j) (hG j)
  have hn : ∀ n, μ0 * (∫ w, ρ w * F n w ∂μ) +
        (1 / 2 : ℝ) * ∑ k, (∫ w, V w k * ∑ j, w.1 0 j k * Gs n w j ∂μ) -
        lam * (∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * Gs n w j ∂μ) =
      ∫ w, f w * F n w ∂μ := by
    intro n
    have h := weak_form_tests hd lam Q hQ hρm hρ heq hK hVm hV hρV (hF n)
    have e2 : ∀ k, ∫ w, V w k * ∑ j, w.1 0 j k * horizontalDerivative j (F n) w ∂μ =
        ∫ w, V w k * ∑ j, w.1 0 j k * Gs n w j ∂μ := fun k =>
      integral_congr_ae ((hD n).mono fun w hw => by simp only [hw])
    have e3 : ∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j (F n) w
        ∂μ = ∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * Gs n w j ∂μ :=
      integral_congr_ae ((hD n).mono fun w hw => by simp only [hw])
    rw [Finset.sum_congr rfl fun k _ => e2 k, e3] at h
    exact h
  have t1 := tendsto_integral_mul_of_eLpNorm_two hρ hF2 hu hFuc
  have t5 := tendsto_integral_mul_of_eLpNorm_two hf hF2 hu hFuc
  have t2 : ∀ k, Tendsto (fun n => ∫ w, V w k * ∑ j, w.1 0 j k * Gs n w j ∂μ) atTop
      (𝓝 (∫ w, V w k * ∑ j, w.1 0 j k * G w j ∂μ)) := fun k =>
    tendsto_integral_mul_sum_entries (hV k) hK k hGs2 hG hGuc
  have t3 := tendsto_integral_mul_sum_entries hρ hK (firstCoordinateIndex hd) hGs2 hG hGuc
  have hlim := (((t1.const_mul μ0).add
    ((tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun k _ => t2 k).const_mul
      (1 / 2 : ℝ))).sub (t3.const_mul lam))
  exact tendsto_nhds_unique (hlim.congr fun n => hn n) t5

/-- **Elliptic regularity** (Step 2 of Lemma 4.1): an `L²` very weak solution `ρ` of
`μρ - L*ρ = f` with `f ∈ L²` has a weak horizontal gradient `V ∈ L²` and satisfies the `H¹` weak
form, for coefficients that are bounded and Lipschitz along orbits. -/
theorem resolvent_density_H1 (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {μ0 : ℝ} {ρ f : FieldPair d → ℝ}
    (hρm : Measurable ρ) (hρ : MemLp ρ 2 (Carriers.reducedReferenceLaw Q))
    (hfm : Measurable f) (hf : MemLp f 2 (Carriers.reducedReferenceLaw Q))
    (heq : ∀ G : FieldPair d → ℝ, IsHorizontalTest G →
      μ0 * (∫ w, ρ w * G w ∂(Carriers.reducedReferenceLaw Q)) -
        ∫ w, ρ w * envGenerator hd lam G w ∂(Carriers.reducedReferenceLaw Q) =
          ∫ w, f w * G w ∂(Carriers.reducedReferenceLaw Q))
    {K : ℝ} {L : ℝ≥0}
    (hgood : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), (∀ x j k, |w.1 x j k| ≤ K) ∧
      ∀ j k, LipschitzWith L fun y => w.1 y j k) :
    ∃ V : FieldPair d → Vec d, Measurable V ∧
      (∀ j, MemLp (fun w => V w j) 2 (Carriers.reducedReferenceLaw Q)) ∧
      HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ ρ V ∧
      ∀ (u : FieldPair d → ℝ) (G : FieldPair d → Vec d), Measurable u →
        MemLp u 2 (Carriers.reducedReferenceLaw Q) → Measurable G →
        (∀ j, MemLp (fun w => G w j) 2 (Carriers.reducedReferenceLaw Q)) →
        HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ u G →
        μ0 * (∫ w, ρ w * u w ∂(Carriers.reducedReferenceLaw Q)) +
            (1 / 2 : ℝ) * ∑ k, (∫ w, V w k * ∑ j, w.1 0 j k * G w j
              ∂(Carriers.reducedReferenceLaw Q)) -
            lam * (∫ w, ρ w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * G w j
              ∂(Carriers.reducedReferenceLaw Q)) =
          ∫ w, f w * u w ∂(Carriers.reducedReferenceLaw Q) := by
  obtain ⟨V, hVm, hV, hρV⟩ := exists_weak_gradient hd lam Q hQ hρm hρ hfm hf heq hgood
  exact ⟨V, hVm, hV, hρV, fun u G hum hu hGm hG huG => weak_form_H1 hd lam Q hQ hρm hρ hf heq
    (hgood.mono fun w hw => hw.1) hVm hV hρV hum hu hGm hG huG⟩

end EinsteinRelation.Entropy
