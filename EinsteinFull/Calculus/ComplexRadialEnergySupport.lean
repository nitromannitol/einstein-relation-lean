import EinsteinFull.Calculus.ComplexHorizontalChainSupport
import EinsteinFull.Calculus.PhysicalGaugeCoercivitySupport
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Radial nonlinear tests and their anisotropic energy

The real differential of `z ↦ φ(‖z‖²) • z` has a scalar and a radial part.
For a nonnegative increasing weight, the latter contributes a nonnegative
real quadratic form to the actual anisotropic principal energy. These are
pointwise prerequisites for the stationary higher-Lp energy argument.
-/

open MeasureTheory
open scoped BigOperators NNReal

noncomputable section

namespace EinsteinFull

open EinsteinRelation

/-- The real differential of a complex radial profile, with weight `b` and slope `c`. -/
def complexRadialDifferential (b c : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  b • ContinuousLinearMap.id ℝ ℂ + ((2 * c) • innerSL ℝ z).smulRight z

/-- The radial differential acts by the literal scalar and rank-one terms. -/
theorem complexRadialDifferential_apply (b c : ℝ) (z w : ℂ) :
    complexRadialDifferential b c z w =
      b • w + (2 * c * (inner ℝ z w)) • z := by
  simp only [complexRadialDifferential, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]

/-- The radial differential is continuous in all its parameters. -/
theorem continuous_complexRadialDifferential {β : Type*} [TopologicalSpace β]
    {b c : β → ℝ} {z : β → ℂ} (hb : Continuous b) (hc : Continuous c)
    (hz : Continuous z) : Continuous (fun x => complexRadialDifferential (b x) (c x) (z x)) := by
  exact (hb.smul continuous_const).add
    ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous₂.comp
      (((continuous_const.mul hc).smul ((innerSL ℝ).continuous.comp hz)).prodMk hz))

/-- A differentiable real weight gives the full real differential of its complex radial profile. -/
theorem hasFDerivAt_complexRadial {φ : ℝ → ℝ} {c : ℝ} (z : ℂ)
    (hφ : HasDerivAt φ c (‖z‖ ^ 2)) :
    HasFDerivAt (fun w : ℂ => φ (‖w‖ ^ 2) • w)
      (complexRadialDifferential (φ (‖z‖ ^ 2)) c z) z := by
  have h := (hφ.hasFDerivAt.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt).smul
    (hasFDerivAt_id z)
  apply h.congr_fderiv
  ext w
  simp only [complexRadialDifferential_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    innerSL_apply_apply, Function.comp_apply, id_eq, smul_eq_mul]
  module

/-- The radial differential retains the explicit scalar plus radial norm bound. -/
theorem norm_complexRadialDifferential_le (b c : ℝ) (z : ℂ) :
    ‖complexRadialDifferential b c z‖ ≤ |b| + 2 * |c| * ‖z‖ ^ 2 := by
  calc
    ‖complexRadialDifferential b c z‖ ≤
        ‖b • ContinuousLinearMap.id ℝ ℂ‖ + ‖((2 * c) • innerSL ℝ z).smulRight z‖ :=
      norm_add_le _ _
    _ = |b| + 2 * |c| * ‖z‖ ^ 2 := by
      rw [norm_smul, ContinuousLinearMap.norm_id, mul_one,
        ContinuousLinearMap.norm_smulRight_apply, norm_smul, innerSL_apply_norm]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- Uniform bounds on the radial differential give a globally Lipschitz nonlinear test. -/
theorem lipschitzWith_complexRadial {φ ψ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : ∀ s : ℝ, 0 ≤ s → HasDerivAt φ (ψ s) s)
    (hK : ∀ s : ℝ, 0 ≤ s → |φ s| + 2 * |ψ s| * s ≤ K) :
    LipschitzWith K (fun z : ℂ => φ (‖z‖ ^ 2) • z) := by
  have hd (z : ℂ) := hasFDerivAt_complexRadial z (hφ _ (sq_nonneg _))
  apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hd z).differentiableAt)
  intro z
  change ‖fderiv ℝ (fun z : ℂ => φ (‖z‖ ^ 2) • z) z‖ ≤ (K : ℝ)
  rw [(hd z).fderiv]
  exact (norm_complexRadialDifferential_le _ _ _).trans (hK _ (sq_nonneg _))

/-- The radial contribution to the complex anisotropic form is a real quadratic form. -/
theorem complexRadialDifferential_energy {d : ℕ} (A : Mat d)
    (b c : ℝ) (z : ℂ) (G : Fin d → ℂ) :
    (∑ j : Fin d, ∑ k : Fin d,
      star (complexRadialDifferential b c z (G j)) * (A j k : ℂ) * G k).re =
      b * (∑ j : Fin d, ∑ k : Fin d, star (G j) * (A j k : ℂ) * G k).re +
        2 * c * dot (fun j => inner ℝ z (G j))
          (A.mulVec (fun j => inner ℝ z (G j))) := by
  change Complex.reCLM (∑ j : Fin d, ∑ k : Fin d, _) =
    b * Complex.reCLM (∑ j : Fin d, ∑ k : Fin d, _) + _
  simp only [map_sum, Complex.reCLM_apply, complexRadialDifferential_apply, real_inner_eq_re_inner ℂ,
    RCLike.inner_apply, RCLike.re_to_complex, Complex.star_def, Complex.real_smul, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, mul_zero, zero_mul,
    sub_zero, zero_add, add_zero, neg_mul, sub_neg_eq_add]
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Increasing radial weights preserve the entire anisotropic ellipticity lower bound. -/
theorem complexRadialDifferential_energy_lowerBound {d : ℕ} (A : Mat d)
    (m b c : ℝ) (hm : 0 ≤ m) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : ∀ ξ : Vec d, m * euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (z : ℂ) (G : Fin d → ℂ) :
    b * m * (∑ j, ‖G j‖ ^ 2) ≤
      (∑ j : Fin d, ∑ k : Fin d,
        star (complexRadialDifferential b c z (G j)) * (A j k : ℂ) * G k).re := by
  rw [complexRadialDifferential_energy]
  have hbase := mul_le_mul_of_nonneg_left (complex_quadratic_lowerBound A m hA G) hb
  have hrad := hA (fun j => inner ℝ z (G j))
  have hpos : 0 ≤ dot (fun j => inner ℝ z (G j))
      (A.mulVec (fun j => inner ℝ z (G j))) :=
    (mul_nonneg hm (show 0 ≤ euclideanSq (fun j => inner ℝ z (G j)) from
      by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _)).trans hrad
  have hcorr := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc) hpos
  simpa only [mul_assoc] using hbase.trans (le_add_of_nonneg_right hcorr)

/-- A logarithmic slope bound controls the transpose test gradient by its weight. -/
theorem norm_complexRadialDifferential_le_weight (b c q : ℝ) (z : ℂ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hslope : 2 * c * ‖z‖ ^ 2 ≤ q * b) :
    ‖complexRadialDifferential b c z‖ ≤ (1 + q) * b := by
  have h := norm_complexRadialDifferential_le b c z
  rw [abs_of_nonneg hb, abs_of_nonneg hc] at h
  calc
    _ ≤ b + 2 * c * ‖z‖ ^ 2 := h
    _ ≤ b + q * b := add_le_add_right hslope b
    _ = _ := by ring

/-- Smooth bounded radial tests preserve the complete actual stationary strong H1 domain. -/
theorem HasComplexHorizontalGradient.comp_radial {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hf : HasComplexHorizontalGradient Q hQ f G) {φ ψ : ℝ → ℝ} {K : ℝ≥0}
    (hφc : ContinuousOn φ (Set.Ici 0)) (hψc : ContinuousOn ψ (Set.Ici 0))
    (hφ : ∀ s : ℝ, 0 ≤ s → HasDerivAt φ (ψ s) s)
    (hK : ∀ s : ℝ, 0 ≤ s → |φ s| + 2 * |ψ s| * s ≤ K) :
    let hLip := lipschitzWith_complexRadial hφ hK
    let hzero : (fun z : ℂ => φ (‖z‖ ^ 2) • z) 0 = 0 := by simp only [smul_zero]
    let D := fun z : ℂ => complexRadialDifferential (φ (‖z‖ ^ 2)) (ψ (‖z‖ ^ 2)) z
    ∃ H : Fin d → Lp ℂ 2 Q,
      HasComplexHorizontalGradient Q hQ (hLip.compLp hzero f) H ∧
        (∀ j : Fin d, H j =ᵐ[Q] fun a => D (f a) (G j a)) := by
  dsimp only
  have hDc : Continuous (fun z : ℂ =>
      complexRadialDifferential (φ (‖z‖ ^ 2)) (ψ (‖z‖ ^ 2)) z) :=
    continuous_complexRadialDifferential
      (hφc.comp_continuous (continuous_norm.pow 2) (fun z => sq_nonneg ‖z‖))
      (hψc.comp_continuous (continuous_norm.pow 2) (fun z => sq_nonneg ‖z‖)) continuous_id
  have hd (z : ℂ) := hasFDerivAt_complexRadial z (hφ _ (sq_nonneg _))
  let hLip := lipschitzWith_complexRadial hφ hK
  let hzero : (fun z : ℂ => φ (‖z‖ ^ 2) • z) 0 = 0 := by simp only [smul_zero]
  refine ⟨_, hf.compLp hLip hzero hDc hd, ?_⟩
  intro j
  exact MemLp.coeFn_toLp _

end EinsteinFull
