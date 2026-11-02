import EinsteinRelation.Calculus.HorizontalMollification

/-! # Bounded horizontal smoothing derivatives and the real core consumer

Source `paper/main.tex:240–248` (actual horizontal derivatives of the bounded core) and
`paper/main.tex:548–566` (horizontal smoothing `S_δ f = ∫ κ_δ(x) f(T_x ω) dx`).

The orbit of the smoothed observable is the reflected convolution `y ↦ (ζ ⋆ g)(-y)` with
`g x = F(T_{-x} ω)`, by `orbit_horizontalMollify_eq_convolution`. Every literal coordinate
derivative of it is moved onto the smooth compactly supported kernel, with one sign per
reflection, so the bound constant is the `L¹` mass of the kernel's iterated derivative. It is
independent of `F`, `ω`, `x`, and needs no continuity of `F` in the environment.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

private theorem contDiff_coordinateDerivative {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (unitVector i))
  exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

private theorem contDiff_coordinateIterate {d : ℕ} (cs : List (Fin d)) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (coordinateIterate cs f) := by
  induction cs with
  | nil => exact hf
  | cons i rest ih => exact contDiff_coordinateDerivative ih i

private theorem hasCompactSupport_coordinateIterate {d : ℕ} (cs : List (Fin d))
    {f : Vec d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (coordinateIterate cs f) := by
  induction cs with
  | nil => exact hf
  | cons i rest ih => exact ih.fderiv_apply ℝ (unitVector i)

/-- Directional derivative of a convolution with a `C¹` compactly supported left factor. -/
private theorem fderiv_convolution_apply {d : ℕ} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) {g : Vec d → ℝ} (hg : LocallyIntegrable g volume)
    (w v : Vec d) :
    (fderiv ℝ ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d),
        volume] g) w v =
      ((fun x => fderiv ℝ ψ x v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) w := by
  have hint : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL
      (Vec d) (fderiv ℝ ψ t) (g (w - t))) volume :=
    (hψc.fderiv ℝ).convolutionExists_left
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d))
      (hψ.continuous_fderiv one_ne_zero) hg w
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hint v]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => rfl

/-- Moving one coordinate derivative through the reflected convolution gives one sign. -/
private theorem coordinateDerivative_const_mul_convolution_neg {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) {g : Vec d → ℝ}
    (hg : LocallyIntegrable g volume) (c : ℝ) (i : Fin d) (y : Vec d) :
    coordinateDerivative i (fun x => c * (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x)) y =
      -(c * ((coordinateDerivative i ψ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-y)) := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (mod_cast le_top)
  have hK := hψc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hψ1 hg (-y)
  have hneg : HasFDerivAt (fun x : Vec d => -x) (-ContinuousLinearMap.id ℝ (Vec d)) y :=
    (hasFDerivAt_id y).fun_neg
  have hfd : fderiv ℝ (fun x => c * (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x)) y = _ :=
    ((hK.comp y hneg).const_mul c).fderiv
  have hD := fderiv_convolution_apply hψ1 hψc hg (-y) (unitVector i)
  show fderiv ℝ (fun x => c * (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x)) y
      (unitVector i) =
    -(c * ((fun x => fderiv ℝ ψ x (unitVector i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] g) (-y))
  rw [hfd, ← hD]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, map_neg, smul_eq_mul]
  ring

/-- The literal iterated coordinate derivatives of the reflected smoothing are the reflected
convolution with the iterated kernel derivative, with sign `(-1)^length`. -/
private theorem coordinateIterate_orbit_convolution {d : ℕ} {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) {g : Vec d → ℝ}
    (hg : LocallyIntegrable g volume) (cs : List (Fin d)) :
    coordinateIterate cs (fun x => (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x)) =
      fun x => (-1 : ℝ) ^ cs.length *
        ((coordinateIterate cs ζ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x) := by
  induction cs with
  | nil => simp only [coordinateIterate, List.length_nil, pow_zero, one_mul]
  | cons i rest ih =>
    have hψ := contDiff_coordinateIterate rest hζ
    have hψc := hasCompactSupport_coordinateIterate rest hζc
    show coordinateDerivative i (coordinateIterate rest
      (fun x => (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x))) = _
    rw [ih]
    refine funext fun y => ?_
    show coordinateDerivative i (fun x => (-1 : ℝ) ^ rest.length *
        ((coordinateIterate rest ζ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x)) y =
      (-1 : ℝ) ^ (rest.length + 1) *
        ((coordinateDerivative i (coordinateIterate rest ζ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          volume] g) (-y)
    rw [coordinateDerivative_const_mul_convolution_neg hψ hψc hg ((-1 : ℝ) ^ rest.length) i y,
      pow_succ]
    ring

/-- A convolution of an integrable kernel with a pointwise bounded function is bounded by the
kernel's `L¹` mass times the bound. Measurability of `g` is not needed. -/
private theorem abs_convolution_le_of_bound {d : ℕ} {ψ g : Vec d → ℝ}
    (hψ : Integrable ψ volume) {M : ℝ} (hg : ∀ x, |g x| ≤ M) (w : Vec d) :
    |(ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) w| ≤ (∫ t, |ψ t|) * M := by
  have hI : Integrable (fun t => |ψ t| * M) volume := hψ.abs.mul_const M
  have hle : ∀ t, ‖ψ t • g (w - t)‖ ≤ |ψ t| * M := fun t => by
    rw [Real.norm_eq_abs, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)
  have h := norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall hle)
  rw [integral_mul_const, Real.norm_eq_abs] at h
  rw [convolution_lsmul]
  exact h

/-- Literal coordinate derivatives of the bounded horizontal smoothing of a bounded measurable
observable are bounded by a constant independent of the observable's bound, the sample, and the
position. The constant depends only on the dimension, the kernel `ζ`, and the coordinate list. -/
theorem abs_coordinateIterate_orbit_horizontalMollify_le :
    ∀ {d : ℕ} (ζ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
    ∀ cs : List (Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ), 0 ≤ M →
    ∀ F : FieldPair d → ℝ, Measurable F → (∀ ω, |F ω| ≤ M) →
    ∀ ω x, |coordinateIterate cs (orbit (horizontalMollify ζ F) ω) x| ≤ C * M := by
  intro d ζ hζ hζc cs
  refine ⟨∫ t, |coordinateIterate cs ζ t|, integral_nonneg fun t => abs_nonneg _, ?_⟩
  intro M _hM0 F hF hb ω x
  have hH : LocallyIntegrable (fun t : Vec d => orbit F ω (-t)) volume :=
    (locallyIntegrable_const (μ := volume) M).mono
      ((measurable_orbit hF ω).comp measurable_neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        have h : |F (translate (-t) ω)| ≤ |M| := (hb (translate (-t) ω)).trans (le_abs_self M)
        simp only [Real.norm_eq_abs]
        exact h)
  have hfun : orbit (horizontalMollify ζ F) ω = fun y : Vec d =>
      (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun t => orbit F ω (-t))) (-y) :=
    funext (orbit_horizontalMollify_eq_convolution ζ F ω)
  have hval : coordinateIterate cs (orbit (horizontalMollify ζ F) ω) x =
      (-1 : ℝ) ^ cs.length * ((coordinateIterate cs ζ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun t => orbit F ω (-t))) (-x) := by
    rw [hfun]
    exact congrFun (coordinateIterate_orbit_convolution hζ hζc hH cs) x
  have hI : Integrable (coordinateIterate cs ζ) volume :=
    ((contDiff_coordinateIterate cs hζ).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateIterate cs hζc)
  have hbd : ∀ t, |orbit F ω (-t)| ≤ M := fun t => hb (translate (-t) ω)
  rw [hval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_convolution_le_of_bound hI hbd (-x)

/-- The actual bounded horizontal smoothing of a bounded measurable observable is a bounded
smooth orbit core: its measurability, `C∞` orbits, and bounded literal coordinate derivatives
all hold without any continuity of the observable in the environment. -/
theorem isHorizontalTest_horizontalMollify :
    ∀ {d : ℕ} (ζ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
    ∀ F : FieldPair d → ℝ, Measurable F → (∃ M : ℝ, ∀ ω, |F ω| ≤ M) →
    IsHorizontalTest (horizontalMollify ζ F) := by
  intro d ζ hζ hζc F hF hb
  obtain ⟨M, hM⟩ := hb
  unfold IsHorizontalTest
  refine ⟨measurable_horizontalMollify ζ hζ.continuous.measurable hF,
    fun ω => contDiff_orbit_horizontalMollify ζ hζ hζc hF ⟨M, hM⟩ ω, fun cs => ?_⟩
  obtain ⟨C, _hC0, hC⟩ := abs_coordinateIterate_orbit_horizontalMollify_le ζ hζ hζc cs
  exact ⟨C * |M|, fun ω x =>
    hC |M| (abs_nonneg M) F hF (fun ω => (hM ω).trans (le_abs_self M)) ω x⟩

end EinsteinRelation.Correctors
