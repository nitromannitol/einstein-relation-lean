import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic.Linarith
import EinsteinFull.Calculus.ParabolicBridgeC1Ext
import EinsteinFull.Calculus.ParabolicBridgeKernel
import EinsteinFull.Calculus.ParabolicBridgeOsc
import EinsteinFull.Calculus.S5PointwiseSupport
import EinsteinFull.Calculus.CommonSpatialTestsSupport
import EinsteinFull.Calculus.CommonTemporalTestsSupport
import EinsteinFull.Work.W6.SamplewiseTemporalFubiniProof
import EllipticRegularity.Parabolic.Cauchy.Lions.JointField
import EllipticRegularity.Parabolic.Cauchy.Lions.LionsRepresentation

/-! Real and imaginary oscillations of the complex caloric comparison.
These identities use the actual normalized Bochner averages. They do not
construct the comparison with prescribed parabolic boundary values. -/

open MeasureTheory
open scoped ENNReal Convolution

namespace EinsteinFull

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Taking the real part commutes with a normalized average of an integrable
complex function. Integrability is essential for this projection. -/
theorem holder_average_re {f : X → ℂ} (hf : Integrable f μ) :
    (⨍ x, f x ∂μ).re = ⨍ x, (f x).re ∂μ := by
  rw [average_eq, average_eq]
  simp only [Complex.smul_re, smul_eq_mul]
  exact congrArg ((μ.real Set.univ)⁻¹ * ·) (integral_re hf).symm

/-- The imaginary counterpart of `holder_average_re`. -/
theorem holder_average_im {f : X → ℂ} (hf : Integrable f μ) :
    (⨍ x, f x ∂μ).im = ⨍ x, (f x).im ∂μ := by
  rw [average_eq, average_eq]
  simp only [Complex.smul_im, smul_eq_mul]
  exact congrArg ((μ.real Set.univ)⁻¹ * ·) (integral_im hf).symm

/-- The squared complex oscillation is exactly the sum of the squared real
and imaginary oscillations, with the same normalized measure. -/
theorem holder_complex_oscillation_sq [IsFiniteMeasure μ] {f : X → ℂ}
    (hf : MemLp f 2 μ) :
    (⨍ x, ‖f x - (⨍ y, f y ∂μ)‖ ^ 2 ∂μ) =
      (⨍ x, |(f x).re - (⨍ y, (f y).re ∂μ)| ^ 2 ∂μ) +
      (⨍ x, |(f x).im - (⨍ y, (f y).im ∂μ)| ^ 2 ∂μ) := by
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hre := (hf.re.sub (memLp_const (⨍ y, (f y).re ∂μ))).integrable_sq
  have him := (hf.im.sub (memLp_const (⨍ y, (f y).im ∂μ))).integrable_sq
  change Integrable (fun x => ((f x).re - (⨍ y, (f y).re ∂μ)) ^ 2) μ at hre
  change Integrable (fun x => ((f x).im - (⨍ y, (f y).im ∂μ)) ^ 2) μ at him
  have hpoint : (fun x => ‖f x - (⨍ y, f y ∂μ)‖ ^ 2) =
      (fun x => ((f x).re - (⨍ y, (f y).re ∂μ)) ^ 2 +
        ((f x).im - (⨍ y, (f y).im ∂μ)) ^ 2) := by
    funext x
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      holder_average_re hfi, holder_average_im hfi]
    ring
  rw [hpoint, average_fun_add hre him]
  simp only [sq_abs]

/-- Two scalar oscillation contractions combine without increasing the
constant. This is the Euclidean norm of the real/imaginary pair. -/
theorem holder_pair_contraction (a b A B K : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hra : Real.sqrt a ≤ K * Real.sqrt A)
    (hib : Real.sqrt b ≤ K * Real.sqrt B) :
    Real.sqrt (a + b) ≤ K * Real.sqrt (A + B) := by
  have hra2 := sq_le_sq₀ (Real.sqrt_nonneg a)
    (mul_nonneg hK (Real.sqrt_nonneg A)) |>.2 hra
  have hib2 := sq_le_sq₀ (Real.sqrt_nonneg b)
    (mul_nonneg hK (Real.sqrt_nonneg B)) |>.2 hib
  rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hA] at hra2
  rw [mul_pow, Real.sq_sqrt hb, Real.sq_sqrt hB] at hib2
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hK (Real.sqrt_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt (add_nonneg ha hb), Real.sq_sqrt (add_nonneg hA hB)]
  nlinarith only [hra2, hib2]

/-- Real and imaginary interior estimates imply the identical complex
oscillation estimate on the actual two normalized measures. -/
theorem holder_complex_contraction
    {ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X → ℂ} (hμ : MemLp f 2 μ) (hν : MemLp f 2 ν)
    (K : ℝ) (hK : 0 ≤ K)
    (hre : Real.sqrt (⨍ x, |(f x).re - (⨍ y, (f y).re ∂μ)| ^ 2 ∂μ) ≤
      K * Real.sqrt (⨍ x, |(f x).re - (⨍ y, (f y).re ∂ν)| ^ 2 ∂ν))
    (him : Real.sqrt (⨍ x, |(f x).im - (⨍ y, (f y).im ∂μ)| ^ 2 ∂μ) ≤
      K * Real.sqrt (⨍ x, |(f x).im - (⨍ y, (f y).im ∂ν)| ^ 2 ∂ν)) :
    Real.sqrt (⨍ x, ‖f x - (⨍ y, f y ∂μ)‖ ^ 2 ∂μ) ≤
      K * Real.sqrt (⨍ x, ‖f x - (⨍ y, f y ∂ν)‖ ^ 2 ∂ν) := by
  rw [holder_complex_oscillation_sq hμ, holder_complex_oscillation_sq hν]
  exact holder_pair_contraction _ _ _ _ K
    (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    hK hre him

/-- The normalized complex mean minimizes squared distance to constants. -/
theorem holder_complex_mean_minimizes [IsFiniteMeasure μ] {f : X → ℂ}
    (hf : MemLp f 2 μ) (c : ℂ) :
    (⨍ x, ‖f x - (⨍ y, f y ∂μ)‖ ^ 2 ∂μ) ≤
      (⨍ x, ‖f x - c‖ ^ 2 ∂μ) := by
  have hre : Integrable (fun x => ((f x).re - c.re) ^ 2) μ :=
    (hf.re.sub (memLp_const c.re)).integrable_sq
  have him : Integrable (fun x => ((f x).im - c.im) ^ 2) μ :=
    (hf.im.sub (memLp_const c.im)).integrable_sq
  have hpoint : (fun x => ‖f x - c‖ ^ 2) =
      (fun x => ((f x).re - c.re) ^ 2 + ((f x).im - c.im) ^ 2) := by
    funext x
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  rw [holder_complex_oscillation_sq hf, hpoint, average_fun_add hre him]
  apply add_le_add
  · have h := mul_le_mul_of_nonneg_left
      (ParabolicBridge.integral_sq_sub_average_le μ hf.re c.re)
      (inv_nonneg.mpr (measureReal_nonneg (μ := μ) (s := Set.univ)))
    simpa only [average_eq, smul_eq_mul, sq_abs, RCLike.re_eq_complex_re] using h
  · have h := mul_le_mul_of_nonneg_left
      (ParabolicBridge.integral_sq_sub_average_le μ hf.im c.im)
      (inv_nonneg.mpr (measureReal_nonneg (μ := μ) (s := Set.univ)))
    simpa only [average_eq, smul_eq_mul, sq_abs, RCLike.im_eq_complex_im] using h

/-- Minkowski's inequality in the normalized complex L2 norm. -/
theorem holder_sqrt_average_norm_add_le {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (⨍ x, ‖f x + g x‖ ^ 2 ∂μ) ≤
      Real.sqrt (⨍ x, ‖f x‖ ^ 2 ∂μ) + Real.sqrt (⨍ x, ‖g x‖ ^ 2 ∂μ) := by
  have hnorm (v : X → ℂ) (hv : MemLp v 2 μ) :
      Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂μ) = (eLpNorm v 2 μ).toReal := by
    rw [ParabolicBridge.sqrt_integral_sq_eq μ hv.norm,
      eLpNorm_norm v hv.aestronglyMeasurable]
  have hsum := eLpNorm_add_le (f := f) (g := g) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.ne, hg.ne⟩) hsum
  rw [ENNReal.toReal_add hf.ne hg.ne] at hreal
  have hint : Real.sqrt (∫ x, ‖f x + g x‖ ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) + Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    change Real.sqrt (∫ x, ‖(f + g) x‖ ^ 2 ∂μ) ≤ _
    rw [hnorm (f + g) (hf.add hg), hnorm f hf, hnorm g hg]
    exact hreal
  simp only [average_eq, smul_eq_mul,
    Real.sqrt_mul (inv_nonneg.mpr (measureReal_nonneg (μ := μ) (s := Set.univ)))]
  simpa only [mul_add] using mul_le_mul_of_nonneg_left hint
    (Real.sqrt_nonneg (μ.real Set.univ)⁻¹)

/-- Transfer oscillation from an actual comparison `v` to `u`. The error
is the normalized L2 distance of the two functions, with constant one. -/
theorem holder_complex_oscillation_comparison [IsFiniteMeasure μ]
    {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂μ)‖ ^ 2 ∂μ) ≤
      Real.sqrt (⨍ x, ‖u x - v x‖ ^ 2 ∂μ) +
        Real.sqrt (⨍ x, ‖v x - (⨍ y, v y ∂μ)‖ ^ 2 ∂μ) := by
  have htriangle := holder_sqrt_average_norm_add_le
    (hu.sub hv) (hv.sub (memLp_const (⨍ y, v y ∂μ)))
  simp only [Pi.sub_apply, sub_add_sub_cancel] at htriangle
  exact (Real.sqrt_le_sqrt (holder_complex_mean_minimizes hu (⨍ y, v y ∂μ))).trans
    htriangle

/-- A comparison contraction transfers to the original function with the
two actual normalized L2 errors, on the smaller and larger measures. -/
theorem holder_complex_comparison_contraction
    {ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {u v : X → ℂ} (huμ : MemLp u 2 μ) (hvμ : MemLp v 2 μ)
    (huν : MemLp u 2 ν) (hvν : MemLp v 2 ν) {K : ℝ} (hK : 0 ≤ K)
    (hv : Real.sqrt (⨍ x, ‖v x - (⨍ y, v y ∂μ)‖ ^ 2 ∂μ) ≤
      K * Real.sqrt (⨍ x, ‖v x - (⨍ y, v y ∂ν)‖ ^ 2 ∂ν)) :
    Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂μ)‖ ^ 2 ∂μ) ≤
      Real.sqrt (⨍ x, ‖u x - v x‖ ^ 2 ∂μ) +
        K * Real.sqrt (⨍ x, ‖u x - v x‖ ^ 2 ∂ν) +
        K * Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂ν)‖ ^ 2 ∂ν) := by
  have hsmall := holder_complex_oscillation_comparison huμ hvμ
  have hlarge := holder_complex_oscillation_comparison hvν huν
  have hdist (x : X) : ‖v x - u x‖ = ‖u x - v x‖ := norm_sub_rev _ _
  simp only [hdist] at hlarge
  have htransfer := hv.trans (mul_le_mul_of_nonneg_left hlarge hK)
  calc
    _ ≤ Real.sqrt (⨍ x, ‖u x - v x‖ ^ 2 ∂μ) +
        K * (Real.sqrt (⨍ x, ‖u x - v x‖ ^ 2 ∂ν) +
          Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂ν)‖ ^ 2 ∂ν)) :=
      hsmall.trans (add_le_add le_rfl htransfer)
    _ = _ := by ring

/-- The energy integrand of the forced/unforced difference. The drift uses
the gradient `G` of the forced solution, while diffusion uses the gradient
`H` of their difference. No equality between these gradients is assumed. -/
theorem holder_comparison_energy_integrand {d : ℕ}
    {A : Fin d → Fin d → ℝ} {Λ : ℝ} (hA : S5Elliptic A Λ)
    (i : Fin d) (ζ e : ℂ) (G H : Fin d → ℂ) :
    (-(1 / 2 : ℂ) * (∑ j, ∑ k,
        (A j k : ℂ) * H k * (starRingEnd ℂ) (H j)) +
      ζ * (∑ j, (A j i : ℂ) * G j) * (starRingEnd ℂ) e).re ≤
      -(Λ⁻¹ / 2) * (∑ j, ‖H j‖ ^ 2) +
        (2 * Λ * ‖ζ‖) * s5CNrm G * ‖e‖ := by
  have hdiff := s5_coercive hA H
  have hforce := Complex.re_le_norm
    (ζ * (∑ j, (A j i : ℂ) * G j) * (starRingEnd ℂ) e)
  rw [norm_mul, norm_mul, Complex.norm_conj] at hforce
  have hflux := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (s5_row_norm_le hA i G) (norm_nonneg ζ))
    (norm_nonneg e)
  have hhalf : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by
    norm_num
  rw [hhalf, Complex.add_re, Complex.re_ofReal_mul]
  nlinarith only [hdiff, hforce, hflux]

/-- Cauchy--Schwarz for the actual complex drift tested against the comparison
error, allowing a measurable anisotropic matrix field on the integration space.
The bound is independent of the phase of the signed complex force. -/
theorem holder_comparison_drift_integral {d : ℕ}
    {A : X → Fin d → Fin d → ℝ} {Λ : ℝ}
    (hA : ∀ x, S5Elliptic (A x) Λ) (i : Fin d) (ζ : ℂ)
    {G : X → Fin d → ℂ} {e : X → ℂ}
    (hG : MemLp (fun x => s5CNrm (G x)) 2 μ) (he : MemLp e 2 μ) :
    ‖∫ x, ζ * (∑ j, (A x j i : ℂ) * G x j) * (starRingEnd ℂ) (e x) ∂μ‖ ≤
      (2 * Λ * ‖ζ‖) * Real.sqrt (∫ x, s5CNrm (G x) ^ 2 ∂μ) *
        Real.sqrt (∫ x, ‖e x‖ ^ 2 ∂μ) := by
  by_cases hX : Nonempty X
  swap
  · have : IsEmpty X := not_nonempty_iff.mp hX
    simp only [integral_of_isEmpty, Real.sqrt_zero, mul_zero, norm_zero, le_refl]
  obtain ⟨x₀⟩ := hX
  have hΛ := (hA x₀).one_le
  have hpoint (x : X) :
      ‖ζ * (∑ j, (A x j i : ℂ) * G x j) * (starRingEnd ℂ) (e x)‖ ≤
        (2 * Λ * ‖ζ‖) * (s5CNrm (G x) * ‖e x‖) := by
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (s5_row_norm_le (hA x) i (G x)) (norm_nonneg ζ))
      (norm_nonneg (e x))
    nlinarith only [this]
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (Filter.Eventually.of_forall fun x => s5CNrm_nonneg (G x))
    (Filter.Eventually.of_forall fun x => norm_nonneg (e x))
    (by simpa using hG) (by simpa using he.norm)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  have hnonneg : 0 ≤ 2 * Λ * ‖ζ‖ := by positivity
  calc
    _ ≤ ∫ x, ‖ζ * (∑ j, (A x j i : ℂ) * G x j) *
        (starRingEnd ℂ) (e x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (2 * Λ * ‖ζ‖) * (s5CNrm (G x) * ‖e x‖) ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        ((hG.integrable_mul he.norm).const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = (2 * Λ * ‖ζ‖) * (∫ x, s5CNrm (G x) * ‖e x‖ ∂μ) := integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs hnonneg

/-- Close the comparison estimate once the weak energy test and spatial
Poincare inequality have been established. Here `R` is the Poincare constant
on the physical cylinder, so the error has the required factor `R² |ζ|`.
This lemma does not assert the existence or testability of the comparison. -/
theorem holder_comparison_error_of_energy {d : ℕ}
    {A : X → Fin d → Fin d → ℝ} {Λ R : ℝ}
    (hA : ∀ x, S5Elliptic (A x) Λ) (hR : 0 ≤ R) (i : Fin d) (ζ : ℂ)
    {G H : X → Fin d → ℂ} {e : X → ℂ}
    (hG : MemLp (fun x => s5CNrm (G x)) 2 μ) (he : MemLp e 2 μ)
    (henergy : Λ⁻¹ / 2 * (∫ x, ∑ j, ‖H x j‖ ^ 2 ∂μ) ≤
      (∫ x, ζ * (∑ j, (A x j i : ℂ) * G x j) * (starRingEnd ℂ) (e x) ∂μ).re)
    (hpoincare : Real.sqrt (∫ x, ‖e x‖ ^ 2 ∂μ) ≤
      R * Real.sqrt (∫ x, ∑ j, ‖H x j‖ ^ 2 ∂μ)) :
    Real.sqrt (∫ x, ‖e x‖ ^ 2 ∂μ) ≤
      4 * Λ ^ 2 * R ^ 2 * ‖ζ‖ * Real.sqrt (∫ x, s5CNrm (G x) ^ 2 ∂μ) := by
  by_cases hX : Nonempty X
  swap
  · have : IsEmpty X := not_nonempty_iff.mp hX
    simp only [integral_of_isEmpty, Real.sqrt_zero, mul_zero, le_refl]
  obtain ⟨x₀⟩ := hX
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one (hA x₀).one_le
  let N := Real.sqrt (∫ x, ∑ j, ‖H x j‖ ^ 2 ∂μ)
  let F := Real.sqrt (∫ x, s5CNrm (G x) ^ 2 ∂μ)
  let E := Real.sqrt (∫ x, ‖e x‖ ^ 2 ∂μ)
  change E ≤ R * N at hpoincare
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hN2 : N ^ 2 = ∫ x, ∑ j, ‖H x j‖ ^ 2 ∂μ :=
    Real.sq_sqrt (integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hforce := holder_comparison_drift_integral hA i ζ hG he
  have hre := Complex.re_le_norm
    (∫ x, ζ * (∑ j, (A x j i : ℂ) * G x j) * (starRingEnd ℂ) (e x) ∂μ)
  have hbasic : Λ⁻¹ / 2 * N ^ 2 ≤ (2 * Λ * ‖ζ‖) * F * E := by
    rw [hN2]
    exact henergy.trans (hre.trans hforce)
  have hscale := mul_le_mul_of_nonneg_left hbasic (show 0 ≤ 2 * Λ by positivity)
  have hcancel : 2 * Λ * (Λ⁻¹ / 2 * N ^ 2) = N ^ 2 := by
    field_simp [hΛ.ne']
  rw [hcancel] at hscale
  have hcoer : N ^ 2 ≤ 4 * Λ ^ 2 * ‖ζ‖ * F * E := by
    nlinarith only [hscale]
  have hsub := mul_le_mul_of_nonneg_left hpoincare
    (show 0 ≤ 4 * Λ ^ 2 * ‖ζ‖ * F by positivity)
  have hNbound : N ≤ 4 * Λ ^ 2 * ‖ζ‖ * F * R := by
    by_cases hzero : N = 0
    · rw [hzero]
      positivity
    · have hpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hzero)
      nlinarith only [hcoer, hsub, hpos]
  have := mul_le_mul_of_nonneg_left hNbound hR
  change E ≤ _
  nlinarith only [hpoincare, this]


open PDE PDE.Parabolic PDE.Parabolic.Lions Set

/-- Actual compact spacetime tests for the interior comparison problem. -/
def holderComparisonTestSpace (d : ℕ) (U : Set (Vec d)) (s T : ℝ) :
    Submodule ℝ (CauchyTestSpace d s T) where
  carrier := {φ | tsupport (φ : Vec d × ℝ → ℝ) ⊆ U ×ˢ Ioo s T}
  zero_mem' := by
    change tsupport (0 : Vec d × ℝ → ℝ) ⊆ _
    simp only [tsupport_zero, empty_subset]
  add_mem' := by
    intro φ ψ hφ hψ
    exact (tsupport_add (φ : Vec d × ℝ → ℝ) ψ).trans (union_subset hφ hψ)
  smul_mem' := by
    intro c φ hφ
    exact (tsupport_smul_subset_right (fun _ : Vec d × ℝ => c) (φ : Vec d × ℝ → ℝ)).trans hφ

/-- Interior comparison tests have zero initial trace. -/
theorem holderComparisonTestSpace_initialTrace {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (φ : holderComparisonTestSpace d U s T) : cauchyGamma φ.val = 0 := by
  rw [cauchyGamma_apply]
  apply Lp.ext
  filter_upwards [(cauchyTraceFun_memLp φ.val).coeFn_toLp,
    (Lp.coeFn_zero ℝ 2 (volume : Measure (Vec d)))] with x hx hzero
  rw [hx, hzero]
  have houtside : (x, s) ∉ tsupport (φ.val : Vec d × ℝ → ℝ) := by
    intro h
    exact (lt_irrefl s) (φ.property h).2.1
  simpa only [cauchyTraceFun, Pi.zero_apply] using image_eq_zero_of_notMem_tsupport houtside

/-- A limit of interior test graphs belongs to the joint Cauchy graph with zero
initial trace. This permits use of the library's actual weak-gradient theorem. -/
theorem holderComparisonTestSpace_closure {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    {u : CauchyX d s T}
    (hu : u ∈ (LinearMap.range
      ((cauchyJ (d := d) (s := s) (T := T)).comp
        (holderComparisonTestSpace d U s T).subtype)).topologicalClosure) :
    WithLp.toLp 2 (u, (0 : CauchyY d)) ∈
      (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure := by
  let F : CauchyX d s T →L[ℝ] WithLp 2 (CauchyX d s T × CauchyY d) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (CauchyX d s T) (CauchyY d)).symm
      |>.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ (CauchyX d s T)).prod 0)
  let K := (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
    (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure
  have hrange : LinearMap.range
      ((cauchyJ (d := d) (s := s) (T := T)).comp
        (holderComparisonTestSpace d U s T).subtype) ≤ K.comap F.toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    apply (LinearMap.range _).le_topologicalClosure
    refine ⟨φ.val, ?_⟩
    change WithLp.toLp 2 (cauchyJ φ.val, cauchyGamma φ.val) =
      WithLp.toLp 2 (cauchyJ φ.val, 0)
    rw [holderComparisonTestSpace_initialTrace]
  exact (LinearMap.range _).topologicalClosure_minimal hrange
    ((LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
      (cauchyGamma (d := d) (s := s) (T := T)))).isClosed_topologicalClosure.preimage
        F.continuous) hu


/-- The value and spatial-gradient coordinates of an interior graph limit are
an actual distributional gradient pair on the Cauchy slab. -/
theorem holderComparisonTestSpace_weakGradient {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    {u : CauchyX d s T}
    (hu : u ∈ (LinearMap.range
      ((cauchyJ (d := d) (s := s) (T := T)).comp
        (holderComparisonTestSpace d U s T).subtype)).topologicalClosure)
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    ∫ z, cauchyJointValue u z * parSpaceGrad ψ.toFun z i ∂slabMeasure d s T =
      -∫ z, cauchyJointGradient u z i * ψ.toFun z ∂slabMeasure d s T :=
  cauchyClosure_spacetimeWeakGradient (holderComparisonTestSpace_closure hu) ψ i


private noncomputable def holderComparisonValueScaleFiber (d : ℕ) (r : ℝ) :
    WithLp 2 (ℝ × HilbertVec d) →L[ℝ] WithLp 2 (ℝ × HilbertVec d) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (HilbertVec d)).symm.toContinuousLinearMap.comp
    ((r • WithLp.fstL 2 ℝ ℝ (HilbertVec d)).prod (WithLp.sndL 2 ℝ ℝ (HilbertVec d)))

/-- Scale the value coordinate of a comparison graph while keeping its spatial
gradient coordinate. The reciprocal scale gives the radius-normalized graph. -/
noncomputable def holderComparisonValueScale (d : ℕ) (s T r : ℝ) :
    CauchyX d s T →L[ℝ] CauchyX d s T :=
  (holderComparisonValueScaleFiber d r).compLpL 2 (slabMeasure d s T)

/-- Decoding a radius-normalized graph recovers its actual value coordinate. -/
theorem holderComparisonValueScale_inv {d : ℕ} {s T r : ℝ} (hr : r ≠ 0)
    (u : CauchyX d s T) :
    holderComparisonValueScale d s T r (holderComparisonValueScale d s T r⁻¹ u) = u := by
  have hf (w : WithLp 2 (ℝ × HilbertVec d)) :
      holderComparisonValueScaleFiber d r (holderComparisonValueScaleFiber d r⁻¹ w) = w := by
    apply (WithLp.equiv 2 (ℝ × HilbertVec d)).injective
    change (r * (r⁻¹ * (WithLp.ofLp w).1), (WithLp.ofLp w).2) = WithLp.ofLp w
    rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  apply Lp.ext
  filter_upwards [(holderComparisonValueScaleFiber d r).coeFn_compLpL
      (holderComparisonValueScale d s T r⁻¹ u),
    (holderComparisonValueScaleFiber d r⁻¹).coeFn_compLpL u] with z hz hzinv
  change (holderComparisonValueScale d s T r
    (holderComparisonValueScale d s T r⁻¹ u)) z = _ at hz
  change (holderComparisonValueScale d s T r⁻¹ u) z = _ at hzinv
  rw [hz, hzinv]
  exact hf (u z)

private theorem holderComparison_graphClosure_decode
    {V W : Type*} [AddCommMonoid V] [Module ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : V →ₗ[ℝ] W) (encode decode : W →L[ℝ] W)
    (hinv : ∀ w, decode (encode w) = w) {u : W}
    (hu : u ∈ (LinearMap.range (encode.toLinearMap.comp J)).topologicalClosure) :
    decode u ∈ (LinearMap.range J).topologicalClosure := by
  have hrange : LinearMap.range (encode.toLinearMap.comp J) ≤
      (LinearMap.range J).topologicalClosure.comap decode.toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    change decode (encode (J φ)) ∈ (LinearMap.range J).topologicalClosure
    rw [hinv]
    exact (LinearMap.range J).le_topologicalClosure ⟨φ, rfl⟩
  exact (LinearMap.range _).topologicalClosure_minimal hrange
    ((LinearMap.range J).isClosed_topologicalClosure.preimage decode.continuous) hu

/-- Limits of radius-normalized test graphs decode into actual test-graph limits.
Thus normalization in Lions coercivity preserves the distributional gradient. -/
theorem holderComparisonTestSpace_scaledClosure {d : ℕ} {U : Set (Vec d)} {s T r : ℝ}
    (hr : r ≠ 0) {u : CauchyX d s T}
    (hu : u ∈ (LinearMap.range
      ((holderComparisonValueScale d s T r⁻¹).toLinearMap.comp
        ((cauchyJ (d := d) (s := s) (T := T)).comp
          (holderComparisonTestSpace d U s T).subtype))).topologicalClosure) :
    holderComparisonValueScale d s T r u ∈ (LinearMap.range
      ((cauchyJ (d := d) (s := s) (T := T)).comp
        (holderComparisonTestSpace d U s T).subtype)).topologicalClosure := by
  with_reducible
    apply holderComparison_graphClosure_decode
      (V := holderComparisonTestSpace d U s T) (W := CauchyX d s T)
      ((cauchyJ (d := d) (s := s) (T := T)).comp
        (holderComparisonTestSpace d U s T).subtype)
      (holderComparisonValueScale d s T r⁻¹) (holderComparisonValueScale d s T r)
  · exact holderComparisonValueScale_inv hr
  · exact hu

/-- Interior tests vanish at the initial endpoint pointwise, before taking traces. -/
theorem holderComparisonTestSpace_initialValue {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (φ : holderComparisonTestSpace d U s T) (x : Vec d) :
    (φ.val : Vec d × ℝ → ℝ) (x, s) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact (lt_irrefl s) (φ.property h).2.1

/-- The time part of the comparison pairing vanishes on every spatial slice.
Both endpoint values are zero for the actual interior test space. -/
theorem holderComparisonTestSpace_timeSlice {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (hsT : s < T) (φ : holderComparisonTestSpace d U s T) (x : Vec d) :
    ∫ t in Icc s T, (φ.val : Vec d × ℝ → ℝ) (x, t) *
      parTimeDeriv (φ.val : Vec d × ℝ → ℝ) (x, t) = 0 := by
  let q : ℝ → ℝ := fun t => (φ.val : Vec d × ℝ → ℝ) (x, t)
  have hq : ContDiff ℝ 1 q := φ.val.property.1.comp
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x)).prodMk contDiff_id)
  have hchain (t : ℝ) : HasDerivAt q
      (parTimeDeriv (φ.val : Vec d × ℝ → ℝ) (x, t)) t :=
    (φ.val.property.1.differentiable one_ne_zero (x, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have hsq (t : ℝ) : deriv (fun τ => q τ ^ 2) t =
      2 * q t * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) (x, t) := by
    convert ((hchain t).pow 2).deriv using 1
    ring
  have hFTC := intervalIntegral.integral_deriv_eq_sub (a := s) (b := T)
    (fun t _ => ((hq.pow 2).differentiable (by norm_num) t))
    ((hq.pow 2).continuous_deriv (by norm_num)).continuousOn.intervalIntegrable
  calc
    ∫ t in Icc s T, q t * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) (x, t) =
        ∫ t in s..T, q t * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) (x, t) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsT.le]
    _ = (1 / 2 : ℝ) * ∫ t in s..T, deriv (fun τ => q τ ^ 2) t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      change q t * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) (x, t) =
        (1 / 2 : ℝ) * deriv (fun τ => q τ ^ 2) t
      rw [hsq t]
      ring
    _ = 0 := by
      rw [hFTC]
      have hT : q T = 0 := φ.val.property.2.2 x
      have hs : q s = 0 := holderComparisonTestSpace_initialValue φ x
      rw [hT, hs]
      ring

/-- The time pairing is integrable without any coefficient assumptions. -/
theorem holderComparisonTestSpace_timeProduct_integrable
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (φ : holderComparisonTestSpace d U s T) :
    Integrable (fun z => (φ.val : Vec d × ℝ → ℝ) z *
      parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z) (slabMeasure d s T) := by
  let g : Vec d × ℝ → ℝ := fun z => (φ.val : Vec d × ℝ → ℝ) z *
    parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z
  have hc : Continuous g :=
    φ.val.property.1.continuous.mul (continuous_parTimeDeriv φ.val.property.1)
  have hK : HasCompactSupport g := by
    apply hasCompactSupport_of_zero_off φ.val.property.2.1.isCompact
    intro z hz
    change (φ.val : Vec d × ℝ → ℝ) z * _ = 0
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hglobal : Integrable g (volume : Measure (Vec d × ℝ)) :=
    hc.integrable_of_hasCompactSupport hK
  exact hglobal.mono_measure Measure.restrict_le_self

/-- The spacetime time-derivative pairing vanishes for actual interior tests. -/
theorem holderComparisonTestSpace_timePairing {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (hsT : s < T) (φ : holderComparisonTestSpace d U s T) :
    ∫ z, (φ.val : Vec d × ℝ → ℝ) z *
      parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z ∂slabMeasure d s T = 0 := by
  let g : Vec d × ℝ → ℝ := fun z => (φ.val : Vec d × ℝ → ℝ) z *
    parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z
  have hmeasure : slabMeasure d s T =
      (volume : Measure (Vec d)).prod (volume.restrict (Icc s T)) := by
    rw [slabMeasure, PDE.Parabolic.Energy.volume_restrict_prod, Measure.restrict_univ]
  have hrestr : Integrable g (slabMeasure d s T) :=
    holderComparisonTestSpace_timeProduct_integrable φ
  change ∫ z, g z ∂slabMeasure d s T = 0
  rw [hmeasure]
  rw [integral_prod g (by simpa only [← hmeasure] using hrestr)]
  simp only [g, holderComparisonTestSpace_timeSlice hsT φ, integral_zero]

/-- The unforced comparison pairing is exactly its spatial energy. The
coefficient is the actual measurable field, with no reaction term added. -/
theorem holderComparisonTestSpace_energyPairing
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (φ : holderComparisonTestSpace d U s T) :
    inner ℝ (cauchyJ φ.val) (cauchyT (c := 0) ha φ.val) =
      ∫ z, vecDot (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))
        ∂slabMeasure d s T := by
  let μ := slabMeasure d s T
  let f : Vec d × ℝ → ℝ := fun z =>
    inner ℝ (cauchyJ φ.val z) (cauchyT (c := 0) ha φ.val z)
  let g : Vec d × ℝ → ℝ := fun z =>
    (φ.val : Vec d × ℝ → ℝ) z * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z
  have hf : Integrable f μ := MeasureTheory.L2.integrable_inner _ _
  have hg : Integrable g μ := holderComparisonTestSpace_timeProduct_integrable φ
  have hJ := cauchyJFun_memLp φ.val
  have hT := cauchyTFun_memLp (c := 0) ha φ.val
  have heq : (fun z => f z + g z) =ᵐ[μ]
      (fun z => vecDot (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))) := by
    filter_upwards [hJ.coeFn_toLp, hT.coeFn_toLp] with z hzJ hzT
    dsimp only [f, g]
    rw [cauchyJ_apply, cauchyT_apply, hzJ, hzT, WithLp.prod_inner_apply]
    simp only [cauchyJFun, cauchyTFun, WithLp.ofLp_toLp, zero_mul, zero_sub,
      PDE.inner_toHilbertVec_eq_vecDot, RCLike.inner_apply, conj_trivial]
    ring
  calc
    inner ℝ (cauchyJ φ.val) (cauchyT (c := 0) ha φ.val) = ∫ z, f z ∂μ :=
      MeasureTheory.L2.inner_def _ _
    _ = ∫ z, f z + g z ∂μ := by
      rw [integral_add hf hg, holderComparisonTestSpace_timePairing hsT φ, add_zero]
    _ = _ := integral_congr_ae heq

/-- Spatial integration by parts for the square of an actual compact `C¹`
spacetime test. No smooth-approximation or boundary-trace premise is needed. -/
theorem holderComparison_coordinateIBP {d : ℕ} {f : Vec d × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hK : HasCompactSupport f) (i : Fin d) (m : ℝ) :
    (∫ z, f z ^ 2) = -2 *
      ∫ z, parSpaceGrad f z i * (z.1 i - m) * f z := by
  let P : (Vec d × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ (Vec d) ℝ)
  let v : Vec d × ℝ := (basisVec i, 0)
  let F : Vec d × ℝ → ℝ := fun z => f z * f z
  let g : Vec d × ℝ → ℝ := fun z => P z - m
  have hF : ContDiff ℝ 1 F := hf.mul hf
  have hFsupp : HasCompactSupport F := hK.mul_left
  have hg : Continuous g := P.continuous.sub continuous_const
  have hgdiff : Differentiable ℝ g := P.differentiable.sub_const m
  have hgderiv (z : Vec d × ℝ) : (fderiv ℝ g z) v = 1 := by
    have hd := (P.hasFDerivAt.sub (hasFDerivAt_const (x := z) (c := m))).fderiv
    change fderiv ℝ g z = P - 0 at hd
    rw [hd]
    simp only [sub_zero]
    simp [P, v, basisVec]
  have h1 : Integrable (fun z => (fderiv ℝ F z) v * g z) :=
    (((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hg).integrable_of_hasCompactSupport (hFsupp.fderiv_apply ℝ v).mul_right
  have h2 : Integrable (fun z => F z * (fderiv ℝ g z) v) := by
    simpa only [hgderiv, mul_one] using hF.continuous.integrable_of_hasCompactSupport hFsupp
  have h3 : Integrable (fun z => F z * g z) :=
    (hF.continuous.mul hg).integrable_of_hasCompactSupport hFsupp.mul_right
  let : (volume : Measure (Vec d × ℝ)).IsAddHaarMeasure :=
    inferInstanceAs ((volume : Measure (Vec d)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := F) (g := g) (v := v) h1 h2 h3
    (fun z _ => hF.differentiable one_ne_zero z) (fun z _ => hgdiff z)
  have hFderiv (z : Vec d × ℝ) :
      (fderiv ℝ F z) v = 2 * parSpaceGrad f z i * f z := by
    change (fderiv ℝ (f * f) z) v = _
    rw [fderiv_mul (hf.differentiable one_ne_zero z) (hf.differentiable one_ne_zero z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    change f z * parSpaceGrad f z i + f z * parSpaceGrad f z i = _
    ring
  have hleft : (fun z => F z * (fderiv ℝ g z) v) = fun z => f z ^ 2 := by
    funext z
    rw [hgderiv]
    dsimp only [F]
    ring
  have hright : (fun z => (fderiv ℝ F z) v * g z) =
      fun z => 2 * (parSpaceGrad f z i * (z.1 i - m) * f z) := by
    funext z
    rw [hFderiv]
    change 2 * parSpaceGrad f z i * f z * (z.1 i - m) = _
    ring
  rw [hleft, hright, integral_const_mul] at hparts
  linarith only [hparts]

/-- A compact `C¹` spacetime function supported in a spatial strip satisfies
Poincare with the strip radius. This estimate uses one actual spatial derivative. -/
theorem holderComparison_coordinatePoincare {d : ℕ} {f : Vec d × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hK : HasCompactSupport f) (i : Fin d) {m R : ℝ}
    (hR : 0 ≤ R) (hstrip : ∀ z ∈ tsupport f, |z.1 i - m| ≤ R) :
    (∫ z, f z ^ 2) ≤ 4 * R ^ 2 * ∫ z, (parSpaceGrad f z i) ^ 2 := by
  let D : Vec d × ℝ → ℝ := fun z => parSpaceGrad f z i
  have hDc : Continuous D := (continuous_apply i).comp (continuous_parSpaceGrad hf)
  have hDK : HasCompactSupport D := hK.fderiv_apply ℝ (basisVec i, 0)
  have hfsq : Integrable (fun z => f z ^ 2) :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport (by simpa only [pow_two] using hK.mul_left)
  have hDsq : Integrable (fun z => D z ^ 2) :=
    (hDc.pow 2).integrable_of_hasCompactSupport (by simpa only [pow_two] using hDK.mul_left)
  have hterm : Integrable (fun z => -2 * (D z * (z.1 i - m) * f z)) :=
    (((hDc.mul ((continuous_apply i).comp continuous_fst |>.sub continuous_const)).mul
      hf.continuous).integrable_of_hasCompactSupport hK.mul_left).const_mul (-2)
  have hpoint (z : Vec d × ℝ) :
      -2 * (D z * (z.1 i - m) * f z) ≤ f z ^ 2 / 2 + 2 * R ^ 2 * D z ^ 2 := by
    by_cases hz : z ∈ tsupport f
    · have hc : (z.1 i - m) ^ 2 ≤ R ^ 2 :=
        sq_le_sq.mpr (by simpa only [abs_of_nonneg hR] using hstrip z hz)
      have hprod := mul_le_mul_of_nonneg_right hc (sq_nonneg (D z))
      nlinarith only [hprod, sq_nonneg (f z + 2 * D z * (z.1 i - m))]
    · rw [image_eq_zero_of_notMem_tsupport hz]
      nlinarith only [mul_nonneg (sq_nonneg R) (sq_nonneg (D z))]
  have hmono := integral_mono hterm
    ((hfsq.div_const 2).add (hDsq.const_mul (2 * R ^ 2))) hpoint
  change (∫ z, -2 * (D z * (z.1 i - m) * f z)) ≤
    ∫ z, f z ^ 2 / 2 + 2 * R ^ 2 * D z ^ 2 at hmono
  rw [integral_const_mul, ← holderComparison_coordinateIBP hf hK i m,
    integral_add (hfsq.div_const 2) (hDsq.const_mul (2 * R ^ 2)),
    integral_div, integral_const_mul] at hmono
  change (∫ z, f z ^ 2) ≤ (∫ z, f z ^ 2) / 2 +
    (2 * R ^ 2) * (∫ z, (parSpaceGrad f z i) ^ 2) at hmono
  linarith only [hmono]

/-- The strip estimate on the actual comparison slab. The strip hypothesis
is purely geometric and applies to the given spatial domain. -/
theorem holderComparisonTestSpace_coordinatePoincare
    {d : ℕ} {U : Set (Vec d)} {s T m R : ℝ}
    (φ : holderComparisonTestSpace d U s T) (i : Fin d) (hR : 0 ≤ R)
    (hstrip : ∀ x ∈ U, |x i - m| ≤ R) :
    (∫ z, (φ.val : Vec d × ℝ → ℝ) z ^ 2 ∂slabMeasure d s T) ≤
      4 * R ^ 2 * ∫ z, (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z i) ^ 2
        ∂slabMeasure d s T := by
  have hout {z : Vec d × ℝ} (hz : z ∉ (univ : Set (Vec d)) ×ˢ Icc s T) :
      z ∉ tsupport (φ.val : Vec d × ℝ → ℝ) := by
    intro h
    exact hz ⟨mem_univ _, (φ.property h).2.1.le, (φ.property h).2.2.le⟩
  have hvalue : (∫ z, (φ.val : Vec d × ℝ → ℝ) z ^ 2 ∂slabMeasure d s T) =
      ∫ z, (φ.val : Vec d × ℝ → ℝ) z ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (hout hz), zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hgrad : (∫ z, (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z i) ^ 2
      ∂slabMeasure d s T) =
      ∫ z, (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z i) ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    simp only [parSpaceGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) (hout hz),
      zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [hvalue, hgrad]
  exact holderComparison_coordinatePoincare φ.val.property.1 φ.val.property.2.1 i hR
    (fun z hz => hstrip z.1 (φ.property hz).1)

/-- The actual Euclidean ball comparison tests satisfy a radius-scaled
Poincare estimate in the Euclidean gradient energy. -/
theorem holderComparisonTestSpace_euclideanBallPoincare
    {d : ℕ} {x₀ : Vec d} {s T R : ℝ}
    (φ : holderComparisonTestSpace d (euclideanBall x₀ R) s T)
    (i : Fin d) (hR : 0 < R) :
    (∫ z, (φ.val : Vec d × ℝ → ℝ) z ^ 2 ∂slabMeasure d s T) ≤
      4 * R ^ 2 * ∫ z, vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        ∂slabMeasure d s T := by
  have hcoord (j : Fin d) : Integrable
      (fun z => (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) ^ 2)
        (slabMeasure d s T) := by
    have hc : Continuous (fun z => parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) :=
      (continuous_apply j).comp (continuous_parSpaceGrad φ.val.property.1)
    have hK : HasCompactSupport
        (fun z => parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) :=
      φ.val.property.2.1.fderiv_apply ℝ (basisVec j, 0)
    exact ((hc.pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two] using hK.mul_left)).restrict
  have henergy : Integrable
      (fun z => vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))
      (slabMeasure d s T) := by
    simp only [vecNormSq_eq_sum_sq]
    exact integrable_finsetSum _ (fun j _ => hcoord j)
  have hstrip : ∀ x ∈ euclideanBall x₀ R, |x i - x₀ i| ≤ R := by
    intro x hx
    have h := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hx
    exact (abs_apply_le_vecEuclideanNorm (x - x₀) i).trans h.le
  exact (holderComparisonTestSpace_coordinatePoincare φ i hR.le hstrip).trans
    (mul_le_mul_of_nonneg_left
      (integral_mono (hcoord i) henergy (fun z => sq_apply_le_vecNormSq _ i))
      (by positivity))

/-- Pointwise form of value-coordinate normalization in the actual `L²` graph. -/
theorem holderComparisonValueScale_ae {d : ℕ} {s T r : ℝ} (u : CauchyX d s T) :
    holderComparisonValueScale d s T r u =ᵐ[slabMeasure d s T]
      (fun z => WithLp.toLp 2 (r * (WithLp.ofLp (u z)).1, (WithLp.ofLp (u z)).2)) := by
  exact (holderComparisonValueScaleFiber d r).coeFn_compLpL u

/-- The normalized value/gradient graph used in the physical-radius comparison. -/
noncomputable def holderComparisonJ (d : ℕ) (U : Set (Vec d)) (s T r : ℝ) :
    holderComparisonTestSpace d U s T →ₗ[ℝ] CauchyX d s T :=
  (holderComparisonValueScale d s T r⁻¹).toLinearMap.comp
    ((cauchyJ (d := d) (s := s) (T := T)).comp
      (holderComparisonTestSpace d U s T).subtype)

/-- The normalized adjoint operator for the actual generator with diffusion `a/2`. -/
noncomputable def holderComparisonT {d : ℕ} {U : Set (Vec d)} {s T lam Lam : ℝ}
    {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (r : ℝ) :
    holderComparisonTestSpace d U s T →ₗ[ℝ] CauchyX d s T :=
  (1 / 2 : ℝ) • ((holderComparisonValueScale d s T (2 * r)).toLinearMap.comp
    ((cauchyT (c := 0) ha).comp (holderComparisonTestSpace d U s T).subtype))

/-- Actual comparison-test values have integrable squares on the slab. -/
theorem holderComparisonTestSpace_valueSq_integrable
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (φ : holderComparisonTestSpace d U s T) :
    Integrable (fun z => (φ.val : Vec d × ℝ → ℝ) z ^ 2) (slabMeasure d s T) := by
  exact ((φ.val.property.1.continuous.pow 2).integrable_of_hasCompactSupport
    (by simpa only [pow_two] using φ.val.property.2.1.mul_left)).restrict

/-- The Euclidean gradient energy of actual comparison tests is integrable. -/
theorem holderComparisonTestSpace_gradientEnergy_integrable
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (φ : holderComparisonTestSpace d U s T) :
    Integrable (fun z => vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))
      (slabMeasure d s T) := by
  simp only [vecNormSq_eq_sum_sq]
  apply integrable_finsetSum
  intro j _
  have hc : Continuous (fun z => parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) :=
    (continuous_apply j).comp (continuous_parSpaceGrad φ.val.property.1)
  have hK : HasCompactSupport
      (fun z => parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) :=
    φ.val.property.2.1.fderiv_apply ℝ (basisVec j, 0)
  exact ((hc.pow 2).integrable_of_hasCompactSupport
    (by simpa only [pow_two] using hK.mul_left)).restrict

/-- The normalized graph norm is precisely its scaled value and gradient energy. -/
theorem holderComparisonJ_norm_sq {d : ℕ} {U : Set (Vec d)} {s T r : ℝ}
    (φ : holderComparisonTestSpace d U s T) :
    ‖holderComparisonJ d U s T r φ‖ ^ 2 =
      r⁻¹ ^ 2 * (∫ z, (φ.val : Vec d × ℝ → ℝ) z ^ 2 ∂slabMeasure d s T) +
      ∫ z, vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        ∂slabMeasure d s T := by
  have hscale := holderComparisonValueScale_ae (r := r⁻¹) (cauchyJ φ.val)
  have hJ := (cauchyJFun_memLp φ.val).coeFn_toLp
  have heq : (fun z => inner ℝ (holderComparisonJ d U s T r φ z)
      (holderComparisonJ d U s T r φ z)) =ᵐ[slabMeasure d s T]
      (fun z => r⁻¹ ^ 2 * (φ.val : Vec d × ℝ → ℝ) z ^ 2 +
        vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)) := by
    filter_upwards [hscale, hJ] with z hz hzJ
    change inner ℝ (holderComparisonValueScale d s T r⁻¹ (cauchyJ φ.val) z)
      (holderComparisonValueScale d s T r⁻¹ (cauchyJ φ.val) z) = _
    rw [hz, cauchyJ_apply, hzJ, WithLp.prod_inner_apply]
    simp only [cauchyJFun, WithLp.ofLp_toLp, PDE.inner_toHilbertVec_eq_vecDot,
      RCLike.inner_apply, conj_trivial, vecNormSq]
    ring
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def,
    integral_congr_ae heq,
    integral_add ((holderComparisonTestSpace_valueSq_integrable φ).const_mul _)
      (holderComparisonTestSpace_gradientEnergy_integrable φ), integral_const_mul]

/-- Radius normalization makes the ball graph norm controlled by five times
its actual Euclidean gradient energy. -/
theorem holderComparisonJ_norm_sq_le {d : ℕ} {x₀ : Vec d} {s T r : ℝ}
    (φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T)
    (i : Fin d) (hr : 0 < r) :
    ‖holderComparisonJ d (euclideanBall x₀ r) s T r φ‖ ^ 2 ≤
      5 * ∫ z, vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        ∂slabMeasure d s T := by
  rw [holderComparisonJ_norm_sq]
  calc
    _ ≤ r⁻¹ ^ 2 * (4 * r ^ 2 *
        ∫ z, vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
          ∂slabMeasure d s T) +
        ∫ z, vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
          ∂slabMeasure d s T :=
      add_le_add (mul_le_mul_of_nonneg_left
        (holderComparisonTestSpace_euclideanBallPoincare φ i hr) (sq_nonneg _)) le_rfl
    _ = _ := by field_simp; ring

/-- Value-coordinate rescaling leaves the comparison pairing unchanged,
since its time contribution integrates to zero. -/
theorem holderComparisonTestSpace_scaledEnergyPairing
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam p q : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (φ : holderComparisonTestSpace d U s T) :
    inner ℝ (holderComparisonValueScale d s T p (cauchyJ φ.val))
      (holderComparisonValueScale d s T q (cauchyT (c := 0) ha φ.val)) =
      ∫ z, vecDot (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))
        ∂slabMeasure d s T := by
  let μ := slabMeasure d s T
  let f : Vec d × ℝ → ℝ := fun z =>
    inner ℝ (holderComparisonValueScale d s T p (cauchyJ φ.val) z)
      (holderComparisonValueScale d s T q (cauchyT (c := 0) ha φ.val) z)
  let g : Vec d × ℝ → ℝ := fun z =>
    (φ.val : Vec d × ℝ → ℝ) z * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z
  have hf : Integrable f μ := MeasureTheory.L2.integrable_inner _ _
  have hg : Integrable g μ := holderComparisonTestSpace_timeProduct_integrable φ
  have heq : (fun z => f z + (p * q) * g z) =ᵐ[μ]
      (fun z => vecDot (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))) := by
    filter_upwards [holderComparisonValueScale_ae (r := p) (cauchyJ φ.val),
      holderComparisonValueScale_ae (r := q) (cauchyT (c := 0) ha φ.val),
      (cauchyJFun_memLp φ.val).coeFn_toLp,
      (cauchyTFun_memLp (c := 0) ha φ.val).coeFn_toLp] with z hzJ hzT hJ hT
    dsimp only [f, g]
    rw [hzJ, hzT, cauchyJ_apply, cauchyT_apply, hJ, hT, WithLp.prod_inner_apply]
    simp only [cauchyJFun, cauchyTFun, WithLp.ofLp_toLp, zero_mul, zero_sub,
      PDE.inner_toHilbertVec_eq_vecDot, RCLike.inner_apply, conj_trivial]
    ring
  calc
    _ = ∫ z, f z ∂μ := MeasureTheory.L2.inner_def _ _
    _ = ∫ z, f z + (p * q) * g z ∂μ := by
      rw [integral_add hf (hg.const_mul _), integral_const_mul,
        holderComparisonTestSpace_timePairing hsT φ, mul_zero, add_zero]
    _ = _ := integral_congr_ae heq

/-- The normalized actual generator pairing is half the diffusion energy. -/
theorem holderComparisonJT_energyPairing
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam r : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (φ : holderComparisonTestSpace d U s T) :
    inner ℝ (holderComparisonJ d U s T r φ) (holderComparisonT ha r φ) =
      (1 / 2 : ℝ) * ∫ z, vecDot (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))
        ∂slabMeasure d s T := by
  change inner ℝ (holderComparisonValueScale d s T r⁻¹ (cauchyJ φ.val))
    ((1 / 2 : ℝ) • holderComparisonValueScale d s T (2 * r)
      (cauchyT (c := 0) ha φ.val)) = _
  rw [inner_smul_right, holderComparisonTestSpace_scaledEnergyPairing hsT ha φ]

/-- The actual nonsymmetric transpose has the same quadratic form. -/
theorem holderComparison_transpose_quadratic {d : ℕ} (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (matTranspose A) x) = vecDot x (matVecMul A x) := by
  unfold vecDot matVecMul matTranspose
  simp only [Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Measurable coefficient energy is integrable for the actual comparison tests. -/
theorem holderComparisonTestSpace_coefficientEnergy_integrable
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (φ : holderComparisonTestSpace d U s T) :
    Integrable (fun z => vecDot (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
      (matVecMul (matTranspose (a z)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)))
      (slabMeasure d s T) := by
  have hinner : Integrable (fun z => inner ℝ (cauchyJ φ.val z)
      (holderComparisonValueScale d s T 0 (cauchyT (c := 0) ha φ.val) z))
      (slabMeasure d s T) := MeasureTheory.L2.integrable_inner _ _
  apply (integrable_congr ?_).mp hinner
  filter_upwards [holderComparisonValueScale_ae (r := 0) (cauchyT (c := 0) ha φ.val),
    (cauchyJFun_memLp φ.val).coeFn_toLp,
    (cauchyTFun_memLp (c := 0) ha φ.val).coeFn_toLp] with z hz hJ hT
  rw [hz, cauchyJ_apply, cauchyT_apply, hJ, hT, WithLp.prod_inner_apply]
  simp only [cauchyJFun, cauchyTFun, WithLp.ofLp_toLp, zero_mul,
    PDE.inner_toHilbertVec_eq_vecDot, RCLike.inner_apply, conj_trivial, zero_add]

/-- Actual ellipticity controls the Euclidean gradient energy in the comparison. -/
theorem holderComparisonTestSpace_energy_lower
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (φ : holderComparisonTestSpace d U s T) :
    lam * (∫ z, vecNormSq (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
      ∂slabMeasure d s T) ≤
      ∫ z, vecDot (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))
        ∂slabMeasure d s T := by
  have hpoint : (fun z => lam * vecNormSq
      (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)) ≤ᵐ[slabMeasure d s T]
      (fun z => vecDot (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z)
        (matVecMul (matTranspose (a z)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))) := by
    filter_upwards [ha.elliptic] with z hz
    rw [holderComparison_transpose_quadratic]
    exact hz.2.2.1 _
  simpa only [integral_const_mul] using integral_mono_ae
    ((holderComparisonTestSpace_gradientEnergy_integrable φ).const_mul lam)
    (holderComparisonTestSpace_coefficientEnergy_integrable ha φ) hpoint

/-- Ellipticity on a nonempty time slab supplies its actual positive constant. -/
theorem holderComparison_lam_pos {d : ℕ} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) : 0 < lam := by
  have hslab : slabMeasure d s T ≠ 0 := by
    have hB : 0 < volume (euclideanBall (0 : Vec d) 1) :=
      volume_euclideanBall_pos 0 (by norm_num)
    have hI : 0 < volume (Ioo s T) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hsT)
    have hrect : 0 < volume (euclideanBall (0 : Vec d) 1 ×ˢ Ioo s T) := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_pos hB.ne' hI.ne'
    have hsub : euclideanBall (0 : Vec d) 1 ×ˢ Ioo s T ⊆
        (univ : Set (Vec d)) ×ˢ Icc s T := by
      intro z hz
      exact ⟨mem_univ _, hz.2.1.le, hz.2.2.le⟩
    have hdomain : 0 < volume ((univ : Set (Vec d)) ×ˢ Icc s T) :=
      hrect.trans_le (measure_mono hsub)
    intro hzero
    have hval := congrArg (fun μ : Measure (Vec d × ℝ) => μ univ) hzero
    rw [slabMeasure, Measure.restrict_apply_univ] at hval
    exact hdomain.ne' (by simpa using hval)
  let : NeZero (slabMeasure d s T) := ⟨hslab⟩
  obtain ⟨z, hz⟩ := ha.elliptic.exists
  exact hz.1

/-- Coercivity of the actual radius-normalized graph, with structural constant
`lam/10` and no artificial reaction term. -/
theorem holderComparison_coercivity
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d)
    (φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T) :
    (lam / 10) * ‖holderComparisonJ d (euclideanBall x₀ r) s T r φ‖ ^ 2 ≤
      inner ℝ (holderComparisonJ d (euclideanBall x₀ r) s T r φ)
        (holderComparisonT ha r φ) := by
  rw [holderComparisonJT_energyPairing hsT ha φ]
  have hn := holderComparisonJ_norm_sq_le φ i hr
  have he := holderComparisonTestSpace_energy_lower ha φ
  have hlam := holderComparison_lam_pos hsT ha
  have hscaled := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ lam / 10)
  linarith only [hscaled, he]

/-- Lions representation in the actual radius-normalized comparison graph.
The represented solution lies in the test-graph closure and has the structural
energy bound; the datum is an arbitrary actual element of the slab Hilbert space. -/
theorem holderComparison_representation
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d) (f : CauchyX d s T) :
    ∃ z ∈ (LinearMap.range
        (holderComparisonJ d (euclideanBall x₀ r) s T r)).topologicalClosure,
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
        inner ℝ z (holderComparisonT (U := euclideanBall x₀ r) ha r φ) =
        inner ℝ f (holderComparisonJ d (euclideanBall x₀ r) s T r φ)) ∧
      ‖z‖ ≤ ‖f‖ / (lam / 10) := by
  have hlam := holderComparison_lam_pos hsT ha
  with_reducible exact (lions_representation_with_norm_bound
    (V := holderComparisonTestSpace d (euclideanBall x₀ r) s T)
    (X := CauchyX d s T)
    (holderComparisonJ d (euclideanBall x₀ r) s T r)
    (holderComparisonT (U := euclideanBall x₀ r) ha r)
    (by positivity : 0 < lam / 10)
    (holderComparison_coercivity (x₀ := x₀) hsT ha hr i) f)

/-- The normalized scalar forcing datum, with zero gradient coordinate. -/
theorem holderComparisonSource_memLp {d : ℕ} {s T r : ℝ}
    {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (slabMeasure d s T)) :
    MemLp (fun z => WithLp.toLp 2 (r * g z, (0 : HilbertVec d))) 2
      (slabMeasure d s T) := by
  rw [MeasureTheory.memLp_prodLp_iff]
  constructor
  · simpa using hg.const_mul r
  · simp

/-- A genuine L² scalar source as an element of the comparison Hilbert space. -/
noncomputable def holderComparisonSource {d : ℕ} {s T : ℝ} (r : ℝ)
    {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (slabMeasure d s T)) : CauchyX d s T :=
  (holderComparisonSource_memLp (r := r) hg).toLp _

/-- The normalized source pairs with the normalized graph as the actual forcing. -/
theorem holderComparisonSource_pairing {d : ℕ} {U : Set (Vec d)} {s T r : ℝ}
    (hr : r ≠ 0) {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (slabMeasure d s T))
    (φ : holderComparisonTestSpace d U s T) :
    inner ℝ (holderComparisonSource r hg) (holderComparisonJ d U s T r φ) =
      ∫ z, g z * (φ.val : Vec d × ℝ → ℝ) z ∂slabMeasure d s T := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(holderComparisonSource_memLp (r := r) hg).coeFn_toLp,
    holderComparisonValueScale_ae (r := r⁻¹) (cauchyJ φ.val),
    (cauchyJFun_memLp φ.val).coeFn_toLp] with z hzF hzJ hzφ
  change inner ℝ (holderComparisonSource r hg z)
    (holderComparisonValueScale d s T r⁻¹ (cauchyJ φ.val) z) = _
  rw [show holderComparisonSource r hg z =
      WithLp.toLp 2 (r * g z, (0 : HilbertVec d)) from hzF,
    hzJ, cauchyJ_apply, hzφ, WithLp.prod_inner_apply]
  simp only [cauchyJFun, WithLp.ofLp_toLp, inner_zero_left, add_zero,
    RCLike.inner_apply, conj_trivial]
  field_simp

/-- The source norm has exactly the physical-radius factor in the error bound. -/
theorem holderComparisonSource_norm_sq {d : ℕ} {s T r : ℝ}
    {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (slabMeasure d s T)) :
    ‖holderComparisonSource r hg‖ ^ 2 =
      r ^ 2 * ∫ z, g z ^ 2 ∂slabMeasure d s T := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  have heq : (fun z => inner ℝ (holderComparisonSource r hg z)
      (holderComparisonSource r hg z)) =ᵐ[slabMeasure d s T]
      (fun z => r ^ 2 * g z ^ 2) := by
    filter_upwards [(holderComparisonSource_memLp (r := r) hg).coeFn_toLp] with z hz
    change inner ℝ ((holderComparisonSource_memLp (r := r) hg).toLp _ z)
      ((holderComparisonSource_memLp (r := r) hg).toLp _ z) = _
    rw [hz, WithLp.prod_inner_apply]
    simp only [inner_zero_left, add_zero, RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae heq, integral_const_mul]

/-- Lions representation for an actual scalar source, with its physical forcing
integral and its quantitative normalized graph estimate. -/
theorem holderComparison_source_representation
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d) {g : Vec d × ℝ → ℝ}
    (hg : MemLp g 2 (slabMeasure d s T)) :
    ∃ z ∈ (LinearMap.range
        (holderComparisonJ d (euclideanBall x₀ r) s T r)).topologicalClosure,
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
        inner ℝ z (holderComparisonT (U := euclideanBall x₀ r) ha r φ) =
          ∫ x, g x * (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) ∧
      ‖z‖ ≤ ‖holderComparisonSource r hg‖ / (lam / 10) := by
  obtain ⟨z, hz, hweak, hnorm⟩ :=
    holderComparison_representation hsT ha hr i (holderComparisonSource r hg)
  refine ⟨z, hz, ?_, hnorm⟩
  intro φ
  rw [hweak φ, holderComparisonSource_pairing hr.ne' hg φ]

/-- Decoding the normalized adjoint pairing gives the actual weak heat operator
with diffusion `a/2`, without a normalization factor in the time derivative. -/
theorem holderComparison_decoded_pairing
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam r : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (z : CauchyX d s T)
    (φ : holderComparisonTestSpace d U s T) :
    inner ℝ z (holderComparisonT ha r φ) =
      ∫ x, -(cauchyJointValue (holderComparisonValueScale d s T r z) x *
          parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x) +
        (1 / 2 : ℝ) * vecDot
          (cauchyJointGradient (holderComparisonValueScale d s T r z) x)
          (matVecMul (matTranspose (a x))
            (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T := by
  change inner ℝ z ((1 / 2 : ℝ) •
    holderComparisonValueScale d s T (2 * r) (cauchyT (c := 0) ha φ.val)) = _
  rw [inner_smul_right, MeasureTheory.L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [holderComparisonValueScale_ae (r := r) z,
    holderComparisonValueScale_ae (r := 2 * r) (cauchyT (c := 0) ha φ.val),
    (cauchyTFun_memLp (c := 0) ha φ.val).coeFn_toLp] with x hx hzT hT
  rw [hzT, cauchyT_apply, hT, WithLp.prod_inner_apply]
  simp only [cauchyTFun, WithLp.ofLp_toLp, zero_mul, zero_sub,
    cauchyJointValue, cauchyJointGradient, hx,
    RCLike.inner_apply, conj_trivial]
  rw [← PDE.Vec.toHilbertVec_toVec ((z x).ofLp.2),
    PDE.inner_toHilbertVec_eq_vecDot]
  simp only [WithLp.fst, WithLp.snd, PDE.HilbertVec.toVec_toHilbertVec]
  ring

/-- An actual scalar source has a physical weak comparison solution. Its
normalized joint field has the Lions estimate, and decoding recovers the actual
spatial graph closure; no boundary trace is inferred from this L² closure. -/
theorem holderComparison_weak_source_solution
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d) {g : Vec d × ℝ → ℝ}
    (hg : MemLp g 2 (slabMeasure d s T)) :
    ∃ z : CauchyX d s T,
      holderComparisonValueScale d s T r z ∈ (LinearMap.range
        ((cauchyJ (d := d) (s := s) (T := T)).comp
          (holderComparisonTestSpace d (euclideanBall x₀ r) s T).subtype)).topologicalClosure ∧
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
        (∫ x, -(cauchyJointValue (holderComparisonValueScale d s T r z) x *
            parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x) +
          (1 / 2 : ℝ) * vecDot
            (cauchyJointGradient (holderComparisonValueScale d s T r z) x)
            (matVecMul (matTranspose (a x))
              (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T) =
          ∫ x, g x * (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) ∧
      ‖z‖ ≤ ‖holderComparisonSource r hg‖ / (lam / 10) := by
  obtain ⟨z, hz, hweak, hnorm⟩ := holderComparison_source_representation hsT ha hr i hg
  refine ⟨z, holderComparisonTestSpace_scaledClosure hr.ne' hz, ?_, hnorm⟩
  intro φ
  rw [← holderComparison_decoded_pairing ha z φ]
  exact hweak φ

/-- The physical value error is controlled by the normalized joint-field norm. -/
theorem holderComparison_decoded_valueSq_le {d : ℕ} {s T r : ℝ}
    (z : CauchyX d s T) :
    (∫ x, cauchyJointValue (holderComparisonValueScale d s T r z) x ^ 2
      ∂slabMeasure d s T) ≤ r ^ 2 * ‖z‖ ^ 2 := by
  have heq : (fun x => cauchyJointValue
      (holderComparisonValueScale d s T r z) x ^ 2) =ᵐ[slabMeasure d s T]
      (fun x => r ^ 2 * cauchyJointValue z x ^ 2) := by
    filter_upwards [holderComparisonValueScale_ae (r := r) z] with x hx
    simp only [cauchyJointValue, hx, WithLp.fst, WithLp.ofLp_toLp, mul_pow]
  rw [integral_congr_ae heq, integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_mono (cauchyJointValue_memLp z).integrable_sq
    (MeasureTheory.L2.integrable_inner _ _)
  intro x
  change cauchyJointValue z x ^ 2 ≤ inner ℝ (z x) (z x)
  rw [real_inner_self_eq_norm_sq, WithLp.prod_norm_sq_eq_of_L2]
  simp only [cauchyJointValue, Real.norm_eq_abs, sq_abs]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The quantitative scalar-source error has the required fourth power of the
physical radius at the squared-value level. -/
theorem holderComparison_source_valueSq_le
    {d : ℕ} {s T r lam : ℝ} {g : Vec d × ℝ → ℝ}
    (hg : MemLp g 2 (slabMeasure d s T))
    {z : CauchyX d s T}
    (hz : ‖z‖ ≤ ‖holderComparisonSource r hg‖ / (lam / 10)) :
    (∫ x, cauchyJointValue (holderComparisonValueScale d s T r z) x ^ 2
      ∂slabMeasure d s T) ≤
        r ^ 4 * (∫ x, g x ^ 2 ∂slabMeasure d s T) / (lam / 10) ^ 2 := by
  calc
    _ ≤ r ^ 2 * ‖z‖ ^ 2 := holderComparison_decoded_valueSq_le z
    _ ≤ r ^ 2 * (‖holderComparisonSource r hg‖ / (lam / 10)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hz 2) (sq_nonneg r)
    _ = _ := by rw [div_pow, holderComparisonSource_norm_sq hg]; ring

/-- Unit decoding preserves the actual joint value/gradient field. -/
theorem holderComparisonValueScale_one {d : ℕ} {s T : ℝ} (u : CauchyX d s T) :
    holderComparisonValueScale d s T 1 u = u := by
  apply Lp.ext
  filter_upwards [holderComparisonValueScale_ae (r := 1) u] with x hx
  simpa only [one_mul, WithLp.toLp_ofLp] using hx

/-- The normalized adjoint pairing equals the physical pairing of the decoded
field. This transfers the constructed correction to the original heat equation. -/
theorem holderComparison_decode_pairing
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam r : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (z : CauchyX d s T)
    (φ : holderComparisonTestSpace d U s T) :
    inner ℝ (holderComparisonValueScale d s T r z) (holderComparisonT ha 1 φ) =
      inner ℝ z (holderComparisonT ha r φ) := by
  rw [holderComparison_decoded_pairing, holderComparisonValueScale_one,
    ← holderComparison_decoded_pairing ha z φ]

/-- Subtracting the constructed correction gives an actual unforced comparison
field. The difference belongs to the spatial test-graph closure and satisfies
the quantitative physical L² error estimate. The forced equation is the actual
weak equation of the supplied joint field, rather than a comparison premise. -/
theorem holderComparison_unforced_replacement
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d) (w : CauchyX d s T)
    {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (slabMeasure d s T))
    (hforced : ∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
      inner ℝ w (holderComparisonT ha 1 φ) =
        ∫ x, g x * (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) :
    ∃ v : CauchyX d s T,
      w - v ∈ (LinearMap.range
        ((cauchyJ (d := d) (s := s) (T := T)).comp
          (holderComparisonTestSpace d (euclideanBall x₀ r) s T).subtype)).topologicalClosure ∧
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
        inner ℝ v (holderComparisonT ha 1 φ) = 0) ∧
      (∫ x, cauchyJointValue (w - v) x ^ 2 ∂slabMeasure d s T) ≤
        r ^ 4 * (∫ x, g x ^ 2 ∂slabMeasure d s T) / (lam / 10) ^ 2 := by
  obtain ⟨z, hz, hweak, hnorm⟩ := holderComparison_source_representation hsT ha hr i hg
  let u := holderComparisonValueScale d s T r z
  refine ⟨w - u, ?_, ?_, ?_⟩
  · rw [sub_sub_cancel]
    exact holderComparisonTestSpace_scaledClosure hr.ne' hz
  · intro φ
    rw [inner_sub_left, hforced φ, holderComparison_decode_pairing ha z φ, hweak φ,
      sub_self]
  · rw [sub_sub_cancel]
    exact holderComparison_source_valueSq_le hg hnorm

/-- Spatial weak-gradient orthogonality is preserved by subtracting a comparison
correction from a joint field. This uses the actual compact test jets. -/
theorem holderComparison_unforced_replacement_spatial
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} {w v : CauchyX d s T}
    (hcorrection : w - v ∈ (LinearMap.range
      ((cauchyJ (d := d) (s := s) (T := T)).comp
        (holderComparisonTestSpace d U s T).subtype)).topologicalClosure)
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d)
    (hw : inner ℝ w (cauchySpatialTestJetLp ψ i) = 0) :
    inner ℝ v (cauchySpatialTestJetLp ψ i) = 0 := by
  have h := cauchyClosure_testJet_orthogonal
    (holderComparisonTestSpace_closure hcorrection) ψ i
  rw [inner_sub_left, hw, zero_sub] at h
  exact neg_eq_zero.mp h

/-- Pairing an arbitrary joint field with the time derivative of a compact
interior test is absolutely integrable. -/
theorem holderComparison_timeProduct_integrable
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (w : CauchyX d s T)
    (φ : holderComparisonTestSpace d U s T) :
    Integrable (fun x => cauchyJointValue w x *
      parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x) (slabMeasure d s T) := by
  have hc := continuous_parTimeDeriv φ.val.property.1
  have hK : HasCompactSupport
      (fun x => parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x) := by
    apply hasCompactSupport_of_zero_off φ.val.property.2.1.isCompact
    intro x hx
    have hD : fderiv ℝ (φ.val : Vec d × ℝ → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
    simp [parTimeDeriv, hD]
  have hmem : MemLp (fun x => parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x)
      2 (slabMeasure d s T) := hc.memLp_of_hasCompactSupport hK
  exact (cauchyJointValue_memLp w).integrable_mul hmem

/-- The diffusion pairing is absolutely integrable for the actual coefficient
field. This follows from the adjoint test map and the scalar time pairing. -/
theorem holderComparison_fluxProduct_integrable
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (w : CauchyX d s T)
    (φ : holderComparisonTestSpace d U s T) :
    Integrable (fun x => vecDot (cauchyJointGradient w x)
      (matVecMul (matTranspose (a x))
        (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x))) (slabMeasure d s T) := by
  have hinner : Integrable
      (fun x => inner ℝ (w x) (cauchyT (c := 0) ha φ.val x))
      (slabMeasure d s T) := MeasureTheory.L2.integrable_inner _ _
  have hsum := hinner.add (holderComparison_timeProduct_integrable w φ)
  apply hsum.congr
  filter_upwards [(cauchyTFun_memLp (c := 0) ha φ.val).coeFn_toLp] with x hx
  dsimp only [Pi.add_apply]
  rw [cauchyT_apply, hx, WithLp.prod_inner_apply]
  simp only [cauchyTFun, WithLp.ofLp_toLp, zero_mul, zero_sub,
    cauchyJointValue, cauchyJointGradient, RCLike.inner_apply, conj_trivial]
  rw [← PDE.Vec.toHilbertVec_toVec ((w x).ofLp.2),
    PDE.inner_toHilbertVec_eq_vecDot]
  simp only [WithLp.fst, WithLp.snd]
  ring

/-- The physical adjoint pairing is the difference of the separately
absolutely convergent time and diffusion integrals. -/
theorem holderComparison_physical_pairing
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (w : CauchyX d s T)
    (φ : holderComparisonTestSpace d U s T) :
    inner ℝ w (holderComparisonT ha 1 φ) =
      -(∫ x, cauchyJointValue w x *
        parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) +
      (1 / 2 : ℝ) * (∫ x, vecDot (cauchyJointGradient w x)
        (matVecMul (matTranspose (a x))
          (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T) := by
  rw [holderComparison_decoded_pairing, holderComparisonValueScale_one]
  calc
    _ = (∫ x, -(cauchyJointValue w x *
          parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x) ∂slabMeasure d s T) +
        (∫ x, (1 / 2 : ℝ) * vecDot (cauchyJointGradient w x)
          (matVecMul (matTranspose (a x))
            (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T) :=
      integral_add (holderComparison_timeProduct_integrable w φ).neg
        ((holderComparison_fluxProduct_integrable ha w φ).const_mul _)
    _ = _ := by rw [integral_neg, integral_const_mul]

/-- An unforced joint field satisfies the actual weak heat equation with
diffusion `a/2`, with the time derivative and diffusion integrals separated. -/
theorem holderComparison_unforced_heat
    {d : ℕ} {U : Set (Vec d)} {s T lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (v : CauchyX d s T)
    (hv : ∀ φ : holderComparisonTestSpace d U s T,
      inner ℝ v (holderComparisonT ha 1 φ) = 0)
    (φ : holderComparisonTestSpace d U s T) :
    (∫ x, cauchyJointValue v x *
      parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) =
      (1 / 2 : ℝ) * (∫ x, vecDot (cauchyJointGradient v x)
        (matVecMul (matTranspose (a x))
          (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T) := by
  have h := hv φ
  rw [holderComparison_physical_pairing] at h
  linarith

/-- A time-first compact test on an open cylinder is an actual interior
comparison test after exchanging its coordinates. -/
noncomputable def holderComparisonSpacetimeTest
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (φ : ℝ × Vec d → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ Ioo s T ×ˢ U) : holderComparisonTestSpace d U s T := by
  let ψ : Vec d × ℝ → ℝ := φ ∘ Prod.swap
  have hsupp : tsupport ψ ⊆ U ×ˢ Ioo s T := by
    intro x hx
    have h := hU (tsupport_comp_subset_preimage φ continuous_swap hx)
    exact ⟨h.2, h.1⟩
  refine ⟨⟨ψ, hφ.comp (contDiff_snd.prodMk contDiff_fst),
    hK.comp_homeomorph (Homeomorph.prodComm _ _), ?_⟩, hsupp⟩
  intro x
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  exact (lt_irrefl T) (hsupp hx).2.2

/-- Evaluation of the coordinate-exchanged compact test. -/
theorem holderComparisonSpacetimeTest_apply
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (φ : ℝ × Vec d → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ Ioo s T ×ˢ U) (x : Vec d × ℝ) :
    ((holderComparisonSpacetimeTest φ hφ hK hU).val : Vec d × ℝ → ℝ) x =
      φ x.swap := rfl

/-- The derivative of a coordinate-exchanged test is the original derivative
applied to the exchanged direction. -/
theorem holderComparisonSpacetimeTest_fderiv
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (φ : ℝ × Vec d → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ Ioo s T ×ˢ U) (x y : Vec d × ℝ) :
    fderiv ℝ ((holderComparisonSpacetimeTest φ hφ hK hU).val :
      Vec d × ℝ → ℝ) x y = fderiv ℝ φ x.swap y.swap := by
  have hswap : HasFDerivAt (Prod.swap : Vec d × ℝ → ℝ × Vec d)
      ((ContinuousLinearMap.snd ℝ (Vec d) ℝ).prod
        (ContinuousLinearMap.fst ℝ (Vec d) ℝ)) x :=
    hasFDerivAt_snd.prodMk hasFDerivAt_fst
  have h := ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp x hswap
  change fderiv ℝ (φ ∘ Prod.swap) x y = _
  rw [h.fderiv]
  rfl

/-- The compact spatial test-jet pairing is the sum of the two actual,
absolutely convergent distributional-gradient integrals. -/
theorem holderComparison_spatial_pairing
    {d : ℕ} {s T : ℝ} (w : CauchyX d s T)
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    inner ℝ w (cauchySpatialTestJetLp ψ i) =
      (∫ x, cauchyJointValue w x * parSpaceGrad ψ.toFun x i ∂slabMeasure d s T) +
      (∫ x, cauchyJointGradient w x i * ψ.toFun x ∂slabMeasure d s T) := by
  have hgrad : MemLp (fun x => parSpaceGrad ψ.toFun x i) 2 (slabMeasure d s T) := by
    change MemLp (fun x => (cauchySpatialTestJet ψ i x).fst) 2 (slabMeasure d s T)
    exact (cauchySpatialTestJetFun_memLp ψ i).continuousLinearMap_comp
      (WithLp.fstL 2 ℝ ℝ (HilbertVec d))
  have hψ : MemLp ψ.toFun 2 (slabMeasure d s T) :=
    ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  have hsum :
      (∫ x, cauchyJointValue w x * parSpaceGrad ψ.toFun x i +
        cauchyJointGradient w x i * ψ.toFun x ∂slabMeasure d s T) =
      (∫ x, cauchyJointValue w x * parSpaceGrad ψ.toFun x i ∂slabMeasure d s T) +
      (∫ x, cauchyJointGradient w x i * ψ.toFun x ∂slabMeasure d s T) :=
    integral_add ((cauchyJointValue_memLp w).integrable_mul hgrad)
      ((cauchyJointGradient_memLp w i).integrable_mul hψ)
  rw [MeasureTheory.L2.inner_def, ← hsum]
  apply integral_congr_ae
  filter_upwards [(cauchySpatialTestJetFun_memLp ψ i).coeFn_toLp] with x hx
  change inner ℝ (w x)
    ((cauchySpatialTestJetFun_memLp ψ i).toLp (cauchySpatialTestJet ψ i) x) = _
  rw [hx, cauchySpatialTestJet, WithLp.prod_inner_apply]
  simp only [cauchyJointValue, cauchyJointGradient]
  rw [← PDE.Vec.toHilbertVec_toVec ((w x).ofLp.2),
    PDE.inner_toHilbertVec_eq_vecDot]
  simp [vecDot, basisVec, Pi.single_apply, mul_comm]

/-- Orthogonality to the actual spatial test jet is exactly the
distributional-gradient equation for its value and gradient coordinates. -/
theorem holderComparison_spatial_orthogonal_iff
    {d : ℕ} {s T : ℝ} (w : CauchyX d s T)
    (ψ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) (i : Fin d) :
    inner ℝ w (cauchySpatialTestJetLp ψ i) = 0 ↔
      (∫ x, cauchyJointValue w x * parSpaceGrad ψ.toFun x i ∂slabMeasure d s T) =
        -(∫ x, cauchyJointGradient w x i * ψ.toFun x ∂slabMeasure d s T) := by
  rw [holderComparison_spatial_pairing]
  constructor <;> intro h <;> linarith

/-- An interior comparison test is also a genuine compact parabolic test on
the ambient slab. -/
noncomputable def holderComparisonParTest
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (φ : holderComparisonTestSpace d U s T) :
    ParTestFunction (univ : Set (Vec d)) (interior (Icc s T)) where
  toFun := φ.val
  contDiff := φ.val.property.1
  hasCompactSupport := φ.val.property.2.1
  tsupport_subset := by
    intro x hx
    exact ⟨mem_univ _, by simpa only [interior_Icc] using (φ.property hx).2⟩

/-- Local caloric replacement for an actual forced joint field. All equations
are distributional equations with the supplied coefficients; the output error
has the physical `r⁴` scalar-source estimate. No boundary trace is asserted. -/
theorem holderComparison_caloric_replacement
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d) (w : CauchyX d s T)
    {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (slabMeasure d s T))
    (hgradient : ∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
      ∀ j : Fin d,
      (∫ x, cauchyJointValue w x *
        parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j ∂slabMeasure d s T) =
        -(∫ x, cauchyJointGradient w x j *
          (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T))
    (hforced : ∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
      (∫ x, cauchyJointValue w x *
        parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) =
        (1 / 2 : ℝ) * (∫ x, vecDot (cauchyJointGradient w x)
          (matVecMul (matTranspose (a x))
            (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T) -
        (∫ x, g x * (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T)) :
    ∃ v : CauchyX d s T,
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
        ∀ j : Fin d,
        (∫ x, cauchyJointValue v x *
          parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j ∂slabMeasure d s T) =
          -(∫ x, cauchyJointGradient v x j *
            (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T)) ∧
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
        (∫ x, cauchyJointValue v x *
          parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) =
          (1 / 2 : ℝ) * (∫ x, vecDot (cauchyJointGradient v x)
            (matVecMul (matTranspose (a x))
              (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T)) ∧
      (∫ x, cauchyJointValue (w - v) x ^ 2 ∂slabMeasure d s T) ≤
        r ^ 4 * (∫ x, g x ^ 2 ∂slabMeasure d s T) / (lam / 10) ^ 2 := by
  have hpair : ∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
      inner ℝ w (holderComparisonT ha 1 φ) =
        ∫ x, g x * (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T := by
    intro φ
    rw [holderComparison_physical_pairing, hforced φ]
    ring
  obtain ⟨v, hcorrection, hweak, herror⟩ :=
    holderComparison_unforced_replacement hsT ha hr i w hg hpair
  refine ⟨v, ?_, holderComparison_unforced_heat ha v hweak, herror⟩
  intro φ j
  exact (holderComparison_spatial_orthogonal_iff v (holderComparisonParTest φ) j).mp
    (holderComparison_unforced_replacement_spatial hcorrection
      (holderComparisonParTest φ) j
      ((holderComparison_spatial_orthogonal_iff w (holderComparisonParTest φ) j).mpr
        (hgradient φ j)))

/-- A slab integral whose integrand vanishes outside the open comparison
cylinder is exactly the time-first cylinder integral after exchanging coordinates. -/
theorem holderComparison_slab_integral
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (f : Vec d × ℝ → ℝ)
    (hf : ∀ x, x ∉ U ×ˢ Ioo s T → f x = 0) :
    (∫ x, f x ∂slabMeasure d s T) =
      ∫ z in Ioo s T ×ˢ U, f z.swap := by
  have hsub : U ×ˢ Ioo s T ⊆ (univ : Set (Vec d)) ×ˢ Icc s T :=
    fun _ hx => ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩
  calc
    _ = ∫ x, f x := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hf x (fun h => hx (hsub h)))
    _ = ∫ x in U ×ˢ Ioo s T, f x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm
    _ = _ := by
      simpa only [Measure.volume_eq_prod] using
        (setIntegral_prod_swap U (Ioo s T) f).symm

/-- Every derivative of an interior comparison test vanishes outside its
open cylinder, including at both time endpoints. -/
theorem holderComparisonTestSpace_fderiv_zero
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ}
    (φ : holderComparisonTestSpace d U s T) {x : Vec d × ℝ}
    (hx : x ∉ U ×ˢ Ioo s T) :
    fderiv ℝ (φ.val : Vec d × ℝ → ℝ) x = 0 :=
  image_eq_zero_of_notMem_tsupport
    (fun h => hx (φ.property (tsupport_fderiv_subset ℝ h)))

/-- Scalar slab L² membership restricts to the actual open cylinder and
persists under the exchange from spatial-first to time-first coordinates. -/
theorem holderComparison_cylinder_memLp
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} {f : Vec d × ℝ → ℝ}
    (hf : MemLp f 2 (slabMeasure d s T)) :
    MemLp (fun z : ℝ × Vec d => f z.swap) 2
      (volume.restrict (Ioo s T ×ˢ U)) := by
  have hsub : U ×ˢ Ioo s T ⊆ (univ : Set (Vec d)) ×ˢ Icc s T :=
    fun _ hx => ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩
  have hlocal : MemLp f 2 (volume.restrict (U ×ˢ Ioo s T)) :=
    hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hlocal ⊢
  exact hlocal.comp_measurePreserving Measure.measurePreserving_swap

/-- The transposed adjoint flux is the actual coefficient action on the
gradient tested against the spatial derivative, with all anisotropic entries. -/
theorem holderComparison_flux_sum {d : ℕ} (A : Mat d) (g h : Vec d) :
    vecDot g (matVecMul (matTranspose A) h) =
      ∑ j : Fin d, (∑ k : Fin d, A j k * g k) * h j := by
  simp only [vecDot, matVecMul, matTranspose, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Testing a scalar field against the derivative of an exchanged compact
test gives the identical time-first cylinder integral in the exchanged direction. -/
theorem holderComparisonSpacetimeTest_derivative_integral
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (φ : ℝ × Vec d → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ Ioo s T ×ˢ U) (w : Vec d × ℝ → ℝ) (y : Vec d × ℝ) :
    (∫ x, w x * fderiv ℝ ((holderComparisonSpacetimeTest φ hφ hK hU).val :
      Vec d × ℝ → ℝ) x y ∂slabMeasure d s T) =
      ∫ z in Ioo s T ×ˢ U, w z.swap * fderiv ℝ φ z y.swap := by
  let ψ := holderComparisonSpacetimeTest φ hφ hK hU
  calc
    _ = ∫ z in Ioo s T ×ˢ U, w z.swap *
        fderiv ℝ (ψ.val : Vec d × ℝ → ℝ) z.swap y :=
      holderComparison_slab_integral _ (by
        intro x hx
        rw [holderComparisonTestSpace_fderiv_zero ψ hx]
        simp)
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        dsimp only [ψ]
        rw [holderComparisonSpacetimeTest_fderiv]
        rfl

/-- Testing against an exchanged compact function gives the identical
time-first cylinder integral. -/
theorem holderComparisonSpacetimeTest_value_integral
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (φ : ℝ × Vec d → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ Ioo s T ×ˢ U) (w : Vec d × ℝ → ℝ) :
    (∫ x, w x * ((holderComparisonSpacetimeTest φ hφ hK hU).val :
      Vec d × ℝ → ℝ) x ∂slabMeasure d s T) =
      ∫ z in Ioo s T ×ˢ U, w z.swap * φ z := by
  apply holderComparison_slab_integral
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport
    (fun h => hx ((holderComparisonSpacetimeTest φ hφ hK hU).property h)), mul_zero]

/-- The actual adjoint flux integral becomes the coefficient-gradient
integral appearing in the time-first interior equation. -/
theorem holderComparisonSpacetimeTest_flux_integral
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (φ : ℝ × Vec d → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ Ioo s T ×ˢ U) (a : ParCoeffField d)
    (g : Vec d × ℝ → Vec d) :
    (∫ x, vecDot (g x) (matVecMul (matTranspose (a x))
      (parSpaceGrad ((holderComparisonSpacetimeTest φ hφ hK hU).val :
        Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T) =
      ∫ z in Ioo s T ×ˢ U, ∑ j : Fin d,
        (∑ k : Fin d, a z.swap j k * g z.swap k) *
          fderiv ℝ φ z (0, Pi.single j 1) := by
  let ψ := holderComparisonSpacetimeTest φ hφ hK hU
  calc
    _ = ∫ z in Ioo s T ×ˢ U, vecDot (g z.swap)
        (matVecMul (matTranspose (a z.swap))
          (parSpaceGrad (ψ.val : Vec d × ℝ → ℝ) z.swap)) :=
      holderComparison_slab_integral _ (by
        intro x hx
        have hzero := holderComparisonTestSpace_fderiv_zero ψ hx
        dsimp only [ψ] at hzero
        simp [parSpaceGrad, hzero, matVecMul, vecDot])
    _ = _ := by
      apply integral_congr_ae
      refine ae_of_all _ fun z => ?_
      dsimp only
      rw [holderComparison_flux_sum]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact holderComparisonSpacetimeTest_fderiv φ hφ hK hU z.swap (basisVec j, 0)

/-- The actual slab gradient equation becomes precisely the time-first
cylinder gradient equation used by the interior estimate. -/
theorem holderComparison_cylinder_weakGradient
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (w : CauchyX d s T)
    (hgradient : ∀ ψ : holderComparisonTestSpace d U s T, ∀ j : Fin d,
      (∫ x, cauchyJointValue w x * parSpaceGrad (ψ.val : Vec d × ℝ → ℝ) x j
        ∂slabMeasure d s T) = -(∫ x, cauchyJointGradient w x j *
          (ψ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T))
    (φ : ℝ × Vec d → ℝ) (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ Ioo s T ×ˢ U) (j : Fin d) :
    (∫ z in Ioo s T ×ˢ U, cauchyJointValue w z.swap *
      fderiv ℝ φ z (0, Pi.single j 1)) =
      -(∫ z in Ioo s T ×ˢ U, cauchyJointGradient w z.swap j * φ z) := by
  have h := hgradient (holderComparisonSpacetimeTest φ hφ hK hU) j
  change (∫ x, cauchyJointValue w x *
    fderiv ℝ ((holderComparisonSpacetimeTest φ hφ hK hU).val :
      Vec d × ℝ → ℝ) x (basisVec j, 0) ∂slabMeasure d s T) = _ at h
  rw [holderComparisonSpacetimeTest_derivative_integral,
    holderComparisonSpacetimeTest_value_integral] at h
  exact h

/-- The actual slab heat equation becomes precisely the time-first
anisotropic cylinder equation used by the interior estimate. -/
theorem holderComparison_cylinder_heat
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (a : ParCoeffField d) (w : CauchyX d s T)
    (hheat : ∀ ψ : holderComparisonTestSpace d U s T,
      (∫ x, cauchyJointValue w x * parTimeDeriv (ψ.val : Vec d × ℝ → ℝ) x
        ∂slabMeasure d s T) = (1 / 2 : ℝ) *
          (∫ x, vecDot (cauchyJointGradient w x) (matVecMul (matTranspose (a x))
            (parSpaceGrad (ψ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T))
    (φ : ℝ × Vec d → ℝ) (hφ : ContDiff ℝ 1 φ) (hK : HasCompactSupport φ)
    (hU : tsupport φ ⊆ Ioo s T ×ˢ U) :
    (∫ z in Ioo s T ×ˢ U, cauchyJointValue w z.swap * fderiv ℝ φ z (1, 0)) =
      (1 / 2 : ℝ) * (∫ z in Ioo s T ×ˢ U, ∑ j : Fin d,
        (∑ k : Fin d, a z.swap j k * cauchyJointGradient w z.swap k) *
          fderiv ℝ φ z (0, Pi.single j 1)) := by
  have h := hheat (holderComparisonSpacetimeTest φ hφ hK hU)
  change (∫ x, cauchyJointValue w x *
    fderiv ℝ ((holderComparisonSpacetimeTest φ hφ hK hU).val :
      Vec d × ℝ → ℝ) x (0, 1) ∂slabMeasure d s T) = _ at h
  rw [holderComparisonSpacetimeTest_derivative_integral,
    holderComparisonSpacetimeTest_flux_integral] at h
  exact h


/-- The actual squared difference on an open comparison cylinder is bounded
by the squared value of the joint-field difference on the whole slab. -/
theorem holderComparison_cylinder_error_le
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (w v : CauchyX d s T) :
    (∫ z in Ioo s T ×ˢ U,
      |cauchyJointValue w z.swap - cauchyJointValue v z.swap| ^ 2) ≤
      ∫ x, cauchyJointValue (w - v) x ^ 2 ∂slabMeasure d s T := by
  have hsub : U ×ˢ Ioo s T ⊆ (univ : Set (Vec d)) ×ˢ Icc s T :=
    fun _ hx => ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩
  have hmeasure : volume.restrict (U ×ˢ Ioo s T) ≤ slabMeasure d s T :=
    Measure.restrict_mono hsub le_rfl
  have hdiff : (fun x => |cauchyJointValue w x - cauchyJointValue v x| ^ 2)
      =ᵐ[slabMeasure d s T] (fun x => cauchyJointValue (w - v) x ^ 2) := by
    filter_upwards [Lp.coeFn_sub w v] with x hx
    simp only [cauchyJointValue, hx, sq_abs]
    rfl
  calc
    _ = ∫ x in U ×ˢ Ioo s T,
        |cauchyJointValue w x - cauchyJointValue v x| ^ 2 := by
      simpa only [Measure.volume_eq_prod] using
        setIntegral_prod_swap U (Ioo s T)
          (fun x => |cauchyJointValue w x - cauchyJointValue v x| ^ 2)
    _ = ∫ x in U ×ˢ Ioo s T, cauchyJointValue (w - v) x ^ 2 :=
      integral_congr_ae (ae_mono hmeasure hdiff)
    _ ≤ _ := integral_mono_measure hmeasure (ae_of_all _ fun _ => sq_nonneg _)
      (cauchyJointValue_memLp (w - v)).integrable_sq


/-- Actual scalar and gradient representatives define a joint slab field. -/
theorem holderComparisonField_memLp
    {d : ℕ} {s T : ℝ} {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (slabMeasure d s T))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (slabMeasure d s T)) :
    MemLp (fun x => WithLp.toLp 2 (u x, Vec.toHilbertVec (g x))) 2
      (slabMeasure d s T) := by
  rw [memLp_prodLp_iff]
  exact ⟨hu, memLp_hilbertVec_sum hg⟩

/-- Pack actual value and gradient representatives into the comparison carrier. -/
noncomputable def holderComparisonField
    {d : ℕ} {s T : ℝ} {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (slabMeasure d s T))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (slabMeasure d s T)) :
    CauchyX d s T := (holderComparisonField_memLp hu hg).toLp _

/-- Packing retains the actual value and every gradient coordinate almost everywhere. -/
theorem holderComparisonField_ae
    {d : ℕ} {s T : ℝ} {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (slabMeasure d s T))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (slabMeasure d s T)) :
    ∀ᵐ x ∂slabMeasure d s T,
      cauchyJointValue (holderComparisonField hu hg) x = u x ∧
      cauchyJointGradient (holderComparisonField hu hg) x = g x := by
  filter_upwards [(holderComparisonField_memLp hu hg).coeFn_toLp] with x hx
  change (holderComparisonField hu hg x).fst = u x ∧
    ((holderComparisonField hu hg x).snd).toVec = g x
  rw [show holderComparisonField hu hg x =
    WithLp.toLp 2 (u x, Vec.toHilbertVec (g x)) from hx]
  exact ⟨rfl, rfl⟩

/-- Local L² representatives extend by zero to the slab. No gradient
identity is asserted across the spatial or temporal boundary. -/
theorem holderComparison_local_indicator_memLp
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    {u : Vec d × ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo s T))) :
    MemLp ((U ×ˢ Ioo s T).indicator u) 2 (slabMeasure d s T) := by
  rw [memLp_indicator_iff_restrict (hU.prod measurableSet_Ioo)]
  have hsub : U ×ˢ Ioo s T ⊆ (univ : Set (Vec d)) ×ˢ Icc s T :=
    fun _ hx => ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩
  change MemLp u 2 ((volume.restrict (univ ×ˢ Icc s T)).restrict (U ×ˢ Ioo s T))
  rwa [Measure.restrict_restrict_of_subset hsub]

/-- The canonical comparison carrier for locally L² value/gradient fields. -/
noncomputable def holderComparisonLocalField
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (volume.restrict (U ×ˢ Ioo s T))) :
    CauchyX d s T :=
  holderComparisonField (holderComparison_local_indicator_memLp hU hu)
    (g := fun x j => (U ×ˢ Ioo s T).indicator (fun x => g x j) x)
    (fun j => holderComparison_local_indicator_memLp hU (hg j))

/-- The canonical local carrier agrees with both actual fields on its cylinder. -/
theorem holderComparisonLocalField_ae
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (volume.restrict (U ×ˢ Ioo s T))) :
    ∀ᵐ x ∂volume.restrict (U ×ˢ Ioo s T),
      cauchyJointValue (holderComparisonLocalField hU hu hg) x = u x ∧
      cauchyJointGradient (holderComparisonLocalField hU hu hg) x = g x := by
  have hsub : U ×ˢ Ioo s T ⊆ (univ : Set (Vec d)) ×ˢ Icc s T :=
    fun _ hx => ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩
  have h := holderComparisonField_ae (holderComparison_local_indicator_memLp hU hu)
    (g := fun x j => (U ×ˢ Ioo s T).indicator (fun x => g x j) x)
    (fun j => holderComparison_local_indicator_memLp hU (hg j))
  filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) h,
    ae_restrict_mem (hU.prod measurableSet_Ioo)] with x hx hmem
  refine ⟨?_, ?_⟩
  · exact hx.1.trans (Set.indicator_of_mem hmem u)
  · ext j
    exact (congrFun hx.2 j).trans (Set.indicator_of_mem hmem (fun x => g x j))


/-- Coordinate exchange retains both actual local representatives. -/
theorem holderComparisonLocalField_cylinder_ae
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (volume.restrict (U ×ˢ Ioo s T))) :
    ∀ᵐ z ∂volume.restrict (Ioo s T ×ˢ U),
      cauchyJointValue (holderComparisonLocalField hU hu hg) z.swap = u z.swap ∧
      cauchyJointGradient (holderComparisonLocalField hU hu hg) z.swap = g z.swap := by
  have h := holderComparisonLocalField_ae hU hu hg
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h ⊢
  exact Measure.measurePreserving_swap.quasiMeasurePreserving.ae h

/-- A slab integrand supported in the local cylinder has precisely its
restricted spatial-first integral, without an integrability premise. -/
theorem holderComparison_supported_integral
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (f : Vec d × ℝ → ℝ)
    (hf : ∀ x, x ∉ U ×ˢ Ioo s T → f x = 0) :
    (∫ x, f x ∂slabMeasure d s T) = ∫ x in U ×ˢ Ioo s T, f x := by
  rw [holderComparison_slab_integral f hf]
  simpa only [Measure.volume_eq_prod] using setIntegral_prod_swap U (Ioo s T) f

/-- Compactly supported value pairings of the canonical local carrier are
exactly those of the prescribed physical representative. -/
theorem holderComparisonLocalField_value_pairing
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (volume.restrict (U ×ˢ Ioo s T)))
    (f : Vec d × ℝ → ℝ) (hf : ∀ x, x ∉ U ×ˢ Ioo s T → f x = 0) :
    (∫ x, cauchyJointValue (holderComparisonLocalField hU hu hg) x * f x
      ∂slabMeasure d s T) = ∫ x in U ×ˢ Ioo s T, u x * f x := by
  rw [holderComparison_supported_integral _ (by
    intro x hx
    rw [hf x hx, mul_zero])]
  apply integral_congr_ae
  filter_upwards [holderComparisonLocalField_ae hU hu hg] with x hx
  exact congrArg (· * f x) hx.1

/-- Compactly supported vector pairings of the canonical local carrier are
exactly those of the prescribed physical gradient. -/
theorem holderComparisonLocalField_gradient_pairing
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (volume.restrict (U ×ˢ Ioo s T)))
    (f : Vec d × ℝ → Vec d) (hf : ∀ x, x ∉ U ×ˢ Ioo s T → f x = 0) :
    (∫ x, vecDot (cauchyJointGradient (holderComparisonLocalField hU hu hg) x)
      (f x) ∂slabMeasure d s T) = ∫ x in U ×ˢ Ioo s T, vecDot (g x) (f x) := by
  rw [holderComparison_supported_integral _ (by
    intro x hx
    simp [hf x hx, vecDot])]
  apply integral_congr_ae
  filter_upwards [holderComparisonLocalField_ae hU hu hg] with x hx
  exact congrArg (fun v => vecDot v (f x)) hx.2


/-- The local carrier preserves the distributional spatial gradient equation
for every interior test, without asserting a boundary gradient identity. -/
theorem holderComparisonLocalField_weakGradient
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (volume.restrict (U ×ˢ Ioo s T)))
    (hgrad : ∀ φ : holderComparisonTestSpace d U s T, ∀ j : Fin d,
      (∫ x in U ×ˢ Ioo s T, u x * parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j) =
        -(∫ x in U ×ˢ Ioo s T, g x j * (φ.val : Vec d × ℝ → ℝ) x))
    (φ : holderComparisonTestSpace d U s T) (j : Fin d) :
    (∫ x, cauchyJointValue (holderComparisonLocalField hU hu hg) x *
      parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j ∂slabMeasure d s T) =
      -(∫ x, cauchyJointGradient (holderComparisonLocalField hU hu hg) x j *
        (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) := by
  rw [holderComparisonLocalField_value_pairing hU hu hg _ (by
    intro x hx
    simp [parSpaceGrad, holderComparisonTestSpace_fderiv_zero φ hx])]
  rw [holderComparison_supported_integral _ (by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.property h)), mul_zero])]
  rw [hgrad φ j]
  congr 1
  apply integral_congr_ae
  filter_upwards [holderComparisonLocalField_ae hU hu hg] with x hx
  exact congrArg (fun v : Vec d => v j * (φ.val : Vec d × ℝ → ℝ) x) hx.2.symm

/-- Extending a scalar source by zero preserves its pairing against an
interior test, including when only local integrability is available. -/
theorem holderComparison_indicator_pairing
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    (f : Vec d × ℝ → ℝ) (φ : holderComparisonTestSpace d U s T) :
    (∫ x, (U ×ˢ Ioo s T).indicator f x * (φ.val : Vec d × ℝ → ℝ) x
      ∂slabMeasure d s T) = ∫ x in U ×ˢ Ioo s T, f x * (φ.val : Vec d × ℝ → ℝ) x := by
  rw [holderComparison_supported_integral _ (by
    intro x hx
    rw [Set.indicator_of_notMem hx, zero_mul])]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (hU.prod measurableSet_Ioo)] with x hx
  rw [Set.indicator_of_mem hx]

/-- Packing the local fields retains their actual scalar forced heat equation. -/
theorem holderComparisonLocalField_forced_heat
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    {u : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2 (volume.restrict (U ×ˢ Ioo s T)))
    (a : ParCoeffField d) (f : Vec d × ℝ → ℝ)
    (hheat : ∀ φ : holderComparisonTestSpace d U s T,
      (∫ x in U ×ˢ Ioo s T, u x * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x) =
        (1 / 2 : ℝ) * (∫ x in U ×ˢ Ioo s T, vecDot (g x)
          (matVecMul (matTranspose (a x))
            (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x))) -
        (∫ x in U ×ˢ Ioo s T, f x * (φ.val : Vec d × ℝ → ℝ) x))
    (φ : holderComparisonTestSpace d U s T) :
    (∫ x, cauchyJointValue (holderComparisonLocalField hU hu hg) x *
      parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) =
      (1 / 2 : ℝ) * (∫ x, vecDot
        (cauchyJointGradient (holderComparisonLocalField hU hu hg) x)
        (matVecMul (matTranspose (a x)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x))
        ∂slabMeasure d s T) -
      (∫ x, (U ×ˢ Ioo s T).indicator f x * (φ.val : Vec d × ℝ → ℝ) x
        ∂slabMeasure d s T) := by
  rw [holderComparisonLocalField_value_pairing hU hu hg _ (by
    intro x hx
    simp [parTimeDeriv, holderComparisonTestSpace_fderiv_zero φ hx]),
    holderComparisonLocalField_gradient_pairing hU hu hg _ (by
      intro x hx
      ext j
      simp [matVecMul, parSpaceGrad, holderComparisonTestSpace_fderiv_zero φ hx]),
    holderComparison_indicator_pairing hU f φ]
  exact hheat φ


/-- The zero extension of a scalar source has precisely its local squared norm. -/
theorem holderComparison_indicator_valueSq
    {d : ℕ} {U : Set (Vec d)} {s T : ℝ} (hU : MeasurableSet U)
    (f : Vec d × ℝ → ℝ) :
    (∫ x, ((U ×ˢ Ioo s T).indicator f x) ^ 2 ∂slabMeasure d s T) =
      ∫ x in U ×ˢ Ioo s T, f x ^ 2 := by
  rw [holderComparison_supported_integral _ (by
    intro x hx
    rw [Set.indicator_of_notMem hx]
    norm_num)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (hU.prod measurableSet_Ioo)] with x hx
  rw [Set.indicator_of_mem hx]

/-- Locally L² scalar physical fields with their actual gradient and forced
heat equations admit a caloric comparison on the open Euclidean cylinder.
The error bound uses the prescribed value representative and the local source. -/
theorem holderComparison_local_caloric_replacement
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d)
    {u f : Vec d × ℝ → ℝ} {g : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (euclideanBall x₀ r ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2
      (volume.restrict (euclideanBall x₀ r ×ˢ Ioo s T)))
    (hf : MemLp f 2 (volume.restrict (euclideanBall x₀ r ×ˢ Ioo s T)))
    (hgrad : ∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T, ∀ j : Fin d,
      (∫ x in euclideanBall x₀ r ×ˢ Ioo s T,
        u x * parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j) =
        -(∫ x in euclideanBall x₀ r ×ˢ Ioo s T, g x j * (φ.val : Vec d × ℝ → ℝ) x))
    (hheat : ∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
      (∫ x in euclideanBall x₀ r ×ˢ Ioo s T,
        u x * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x) =
        (1 / 2 : ℝ) * (∫ x in euclideanBall x₀ r ×ˢ Ioo s T, vecDot (g x)
          (matVecMul (matTranspose (a x))
            (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x))) -
        (∫ x in euclideanBall x₀ r ×ˢ Ioo s T, f x * (φ.val : Vec d × ℝ → ℝ) x)) :
    ∃ v : CauchyX d s T,
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T, ∀ j : Fin d,
        (∫ x, cauchyJointValue v x * parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j
          ∂slabMeasure d s T) =
          -(∫ x, cauchyJointGradient v x j * (φ.val : Vec d × ℝ → ℝ) x
            ∂slabMeasure d s T)) ∧
      (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) s T,
        (∫ x, cauchyJointValue v x * parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x
          ∂slabMeasure d s T) =
          (1 / 2 : ℝ) * (∫ x, vecDot (cauchyJointGradient v x)
            (matVecMul (matTranspose (a x)) (parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x))
            ∂slabMeasure d s T)) ∧
      (∫ z in Ioo s T ×ˢ euclideanBall x₀ r,
        |u z.swap - cauchyJointValue v z.swap| ^ 2) ≤
        r ^ 4 * (∫ x in euclideanBall x₀ r ×ˢ Ioo s T, f x ^ 2) / (lam / 10) ^ 2 := by
  let hB := measurableSet_euclideanBall x₀ r
  let w := holderComparisonLocalField hB hu hg
  have hfSlab := holderComparison_local_indicator_memLp hB hf
  obtain ⟨v, hvgrad, hvheat, herror⟩ := holderComparison_caloric_replacement
    hsT ha hr i w hfSlab
    (holderComparisonLocalField_weakGradient hB hu hg hgrad)
    (holderComparisonLocalField_forced_heat hB hu hg a f hheat)
  refine ⟨v, hvgrad, hvheat, ?_⟩
  have hvalues : (fun z : ℝ × Vec d => |u z.swap - cauchyJointValue v z.swap| ^ 2)
      =ᵐ[volume.restrict (Ioo s T ×ˢ euclideanBall x₀ r)]
        (fun z => |cauchyJointValue w z.swap - cauchyJointValue v z.swap| ^ 2) := by
    filter_upwards [holderComparisonLocalField_cylinder_ae hB hu hg] with z hz
    exact congrArg (fun q : ℝ => |q - cauchyJointValue v z.swap| ^ 2) hz.1.symm
  rw [integral_congr_ae hvalues]
  calc
    _ ≤ ∫ x, cauchyJointValue (w - v) x ^ 2 ∂slabMeasure d s T :=
      holderComparison_cylinder_error_le w v
    _ ≤ _ := by
      simpa only [holderComparison_indicator_valueSq hB f] using herror

/-- The literal complex coefficient-column drift is bounded by the full
Euclidean gradient energy, with no dependence on the force phase. -/
theorem holderComparison_drift_sq_le {d : ℕ}
    {A : Fin d → Fin d → ℝ} {Λ : ℝ} (hA : S5Elliptic A Λ)
    (i : Fin d) (ζ : ℂ) (G : Fin d → ℂ) :
    ‖ζ * (∑ j, (A j i : ℂ) * G j)‖ ^ 2 ≤
      (2 * Λ * ‖ζ‖) ^ 2 * (∑ j, ‖G j‖ ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (s5_row_norm_le hA i G) (norm_nonneg ζ)
  rw [← norm_mul] at h
  have he : ‖ζ‖ * (2 * Λ * s5CNrm G) = (2 * Λ * ‖ζ‖) * s5CNrm G := by ring
  rw [he] at h
  have hs := sq_le_sq₀ (norm_nonneg _) (by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hA.one_le]))
      (norm_nonneg ζ)) (s5CNrm_nonneg G)) |>.mpr h
  simpa only [mul_pow, s5CNrm,
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg ‖G j‖)] using hs

/-- Local L² gradients and measurable actual coefficients give a local L²
complex drift, together with its quantitative squared-source integral. -/
theorem holderComparison_drift_memLp_integral {d : ℕ}
    {A : X → Fin d → Fin d → ℝ} {Λ : ℝ}
    (hA : ∀ᵐ x ∂μ, S5Elliptic (A x) Λ)
    (hmA : ∀ j k, AEStronglyMeasurable (fun x => A x j k) μ)
    (i : Fin d) (ζ : ℂ) {G : X → Fin d → ℂ}
    (hG : ∀ j, MemLp (fun x => G x j) 2 μ) :
    MemLp (fun x => ζ * (∑ j, (A x j i : ℂ) * G x j)) 2 μ ∧
      (∫ x, ‖ζ * (∑ j, (A x j i : ℂ) * G x j)‖ ^ 2 ∂μ) ≤
        (2 * Λ * ‖ζ‖) ^ 2 * (∫ x, ∑ j, ‖G x j‖ ^ 2 ∂μ) := by
  have hm : AEStronglyMeasurable
      (fun x => ζ * (∑ j, (A x j i : ℂ) * G x j)) μ := by
    apply AEStronglyMeasurable.const_mul
    have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun j _ =>
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (hmA j i)).mul
        (hG j).aestronglyMeasurable)
    convert hs using 1
    ext x
    simp only [Finset.sum_apply, Pi.mul_apply]
  have henergy : Integrable (fun x => ∑ j, ‖G x j‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => (memLp_two_iff_integrable_sq_norm
      (hG j).aestronglyMeasurable).mp (hG j)
  have hbound : ∀ᵐ x ∂μ,
      ‖ζ * (∑ j, (A x j i : ℂ) * G x j)‖ ^ 2 ≤
        (2 * Λ * ‖ζ‖) ^ 2 * (∑ j, ‖G x j‖ ^ 2) :=
    hA.mono fun x hx => holderComparison_drift_sq_le hx i ζ (G x)
  have hint : Integrable
      (fun x => ‖ζ * (∑ j, (A x j i : ℂ) * G x j)‖ ^ 2) μ := by
    apply (henergy.const_mul ((2 * Λ * ‖ζ‖) ^ 2)).mono' (hm.norm.pow 2)
    filter_upwards [hbound] with x hx
    change |‖ζ * (∑ j, (A x j i : ℂ) * G x j)‖ ^ 2| ≤ _
    rwa [abs_of_nonneg (sq_nonneg _)]
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hint, ?_⟩
  simpa only [integral_const_mul] using
    integral_mono_ae hint (henergy.const_mul ((2 * Λ * ‖ζ‖) ^ 2)) hbound

/-- Both scalar components of the literal drift satisfy the same source
bound. Their L² membership is a consequence of the complex source estimate. -/
theorem holderComparison_drift_components {d : ℕ}
    {A : X → Fin d → Fin d → ℝ} {Λ : ℝ}
    (hA : ∀ᵐ x ∂μ, S5Elliptic (A x) Λ)
    (hmA : ∀ j k, AEStronglyMeasurable (fun x => A x j k) μ)
    (i : Fin d) (ζ : ℂ) {G : X → Fin d → ℂ}
    (hG : ∀ j, MemLp (fun x => G x j) 2 μ) :
    let f := fun x => ζ * (∑ j, (A x j i : ℂ) * G x j)
    MemLp (fun x => (f x).re) 2 μ ∧ MemLp (fun x => (f x).im) 2 μ ∧
      (∫ x, (f x).re ^ 2 ∂μ) + (∫ x, (f x).im ^ 2 ∂μ) ≤
        (2 * Λ * ‖ζ‖) ^ 2 * (∫ x, ∑ j, ‖G x j‖ ^ 2 ∂μ) := by
  dsimp only
  obtain ⟨hf, hbound⟩ := holderComparison_drift_memLp_integral hA hmA i ζ hG
  refine ⟨hf.re, hf.im, ?_⟩
  have hre : Integrable (fun x => (ζ * (∑ j, (A x j i : ℂ) * G x j)).re ^ 2) μ :=
    hf.re.integrable_sq
  have him : Integrable (fun x => (ζ * (∑ j, (A x j i : ℂ) * G x j)).im ^ 2) μ :=
    hf.im.integrable_sq
  rw [← integral_add hre him]
  have he (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simpa only [he] using hbound

/-- Adding a time-dependent spatial constant to a locally integrable field
adds exactly its temporal pairing times the spatial test integral. -/
theorem holderComparison_integral_add_temporal_constant
    {d : ℕ} {ν : Measure ℝ} [SFinite ν] {F : Vec d × ℝ → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K → Integrable F ((volume.restrict K).prod ν))
    {m : ℝ → ℂ} (hm : Integrable m ν)
    {φ : Vec d → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {η : ℝ → ℝ} (hη : Measurable η) {C : ℝ} (hC : ∀ s, ‖η s‖ ≤ C) :
    (∫ x, (∫ s, (η s : ℂ) * (F (x, s) + m s) ∂ν) * φ x) =
      (∫ x, (∫ s, (η s : ℂ) * F (x, s) ∂ν) * φ x) +
        (∫ s, (η s : ℂ) * m s ∂ν) * (∫ x, φ x) := by
  have hmF (K : Set (Vec d)) (hK : IsCompact K) :
      Integrable (fun p : Vec d × ℝ => m p.2) ((volume.restrict K).prod ν) := by
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    simpa only [one_mul] using (integrable_const (1 : ℂ) (μ := volume.restrict K)).mul_prod hm
  have hiF := (CommonTemporalTests.integrable_spatial_mul hF hφ hφc).bdd_mul
    (Complex.measurable_ofReal.comp (hη.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p => by simpa only [Function.comp_apply, Complex.norm_real] using hC p.2)
  have hiM := (CommonTemporalTests.integrable_spatial_mul hmF hφ hφc).bdd_mul
    (Complex.measurable_ofReal.comp (hη.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p => by simpa only [Function.comp_apply, Complex.norm_real] using hC p.2)
  change Integrable (fun p : Vec d × ℝ => (η p.2 : ℂ) * (F p * φ p.1))
    (volume.prod ν) at hiF
  change Integrable (fun p : Vec d × ℝ => (η p.2 : ℂ) * (m p.2 * φ p.1))
    (volume.prod ν) at hiM
  have hpair := CommonTemporalTests.spatial_temporal_pairing
    (fun K hK => (hF K hK).add (hmF K hK)) hφ hφc hη hC
  simp only [Pi.add_apply] at hpair
  rw [hpair.2]
  have he : (fun p : Vec d × ℝ => (η p.2 : ℂ) * ((F p + m p.2) * φ p.1)) =
      (fun p => (η p.2 : ℂ) * (F p * φ p.1) + (η p.2 : ℂ) * (m p.2 * φ p.1)) := by
    funext p
    ring
  rw [he, integral_add hiF hiM,
    ← (CommonTemporalTests.spatial_temporal_pairing hF hφ hφc hη hC).2,
    ← (CommonTemporalTests.spatial_temporal_pairing hmF hφ hφc hη hC).2]
  change _ + (∫ x, (∫ s, (η s : ℂ) * m s ∂ν) * φ x) = _
  rw [integral_const_mul]

/-- A product-integrable parameter family of tests pairs with a physical
field by first integrating the tests. This is the Fubini step for
mollification of separated spacetime tests. -/
theorem holderComparison_parameter_pairing
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SFinite μ] [SFinite ν]
    (u : X → ℂ) (ψ : Y → X → ℂ)
    (hi : Integrable (fun p : Y × X => u p.2 * ψ p.1 p.2) (ν.prod μ)) :
    (∫ y, (∫ x, u x * ψ y x ∂μ) ∂ν) =
      ∫ x, u x * (∫ y, ψ y x ∂ν) ∂μ := by
  rw [integral_integral_swap hi]
  simp only [integral_const_mul]

/-- Averaging separated weak identities gives the weak identity for the
averaged tests. All Fubini hypotheses concern the actual weighted fields. -/
theorem holderComparison_parameter_weak_equation
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SFinite μ] [SFinite ν]
    {ι : Type*} [Fintype ι]
    (u f : X → ℂ) (F : ι → X → ℂ)
    (ψt ψ : Y → X → ℂ) (ψx : ι → Y → X → ℂ)
    (hit : Integrable (fun p : Y × X => u p.2 * ψt p.1 p.2) (ν.prod μ))
    (hix : ∀ j, Integrable (fun p : Y × X => F j p.2 * ψx j p.1 p.2) (ν.prod μ))
    (hi : Integrable (fun p : Y × X => f p.2 * ψ p.1 p.2) (ν.prod μ))
    (hw : ∀ᵐ y ∂ν, (∫ x, u x * ψt y x ∂μ) =
      (∑ j, ∫ x, F j x * ψx j y x ∂μ) + ∫ x, f x * ψ y x ∂μ) :
    (∫ x, u x * (∫ y, ψt y x ∂ν) ∂μ) =
      (∑ j, ∫ x, F j x * (∫ y, ψx j y x ∂ν) ∂μ) +
        ∫ x, f x * (∫ y, ψ y x ∂ν) ∂μ := by
  calc
    _ = ∫ y, (∫ x, u x * ψt y x ∂μ) ∂ν :=
      (holderComparison_parameter_pairing u ψt hit).symm
    _ = ∫ y, ((∑ j, ∫ x, F j x * ψx j y x ∂μ) +
        ∫ x, f x * ψ y x ∂μ) ∂ν := integral_congr_ae hw
    _ = (∑ j, ∫ y, (∫ x, F j x * ψx j y x ∂μ) ∂ν) +
        ∫ y, (∫ x, f x * ψ y x ∂μ) ∂ν := by
      rw [integral_add
        (integrable_finsetSum _ (fun j _ => (hix j).integral_prod_left))
        hi.integral_prod_left,
        integral_finsetSum _ (fun j _ => (hix j).integral_prod_left)]
    _ = _ := by
      rw [holderComparison_parameter_pairing f ψ hi]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact holderComparison_parameter_pairing (F j) (ψx j) (hix j)

/-- Bounded pointwise convergence of complex tests preserves pairings with
an L1 physical field. The measure may already be a local cylinder restriction. -/
theorem holderComparison_pairing_tendsto
    {u : X → ℂ} (hu : Integrable u μ) {ψ : ℕ → X → ℂ} {ψ₀ : X → ℂ}
    (hm : ∀ n, AEStronglyMeasurable (ψ n) μ) {C : ℝ}
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ C)
    (hl : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => ψ n x) Filter.atTop (nhds (ψ₀ x))) :
    Filter.Tendsto (fun n => ∫ x, u x * ψ n x ∂μ) Filter.atTop
      (nhds (∫ x, u x * ψ₀ x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖u x‖ * C)
    (fun n => hu.aestronglyMeasurable.mul (hm n)) (hu.norm.mul_const C) ?_ ?_
  · intro n
    filter_upwards [hb n] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  · filter_upwards [hl] with x hx
    exact hx.const_mul (u x)

/-- The weak equation is closed under bounded pointwise convergence of the
value and derivative tests against locally L1 coefficients. -/
theorem holderComparison_weak_equation_limit
    {ι : Type*} [Fintype ι]
    {u f : X → ℂ} {F : ι → X → ℂ}
    (hu : Integrable u μ) (hf : Integrable f μ) (hF : ∀ j, Integrable (F j) μ)
    {ψt ψ : ℕ → X → ℂ} {ψx : ι → ℕ → X → ℂ}
    {ψt₀ ψ₀ : X → ℂ} {ψx₀ : ι → X → ℂ}
    (hmt : ∀ n, AEStronglyMeasurable (ψt n) μ)
    (hm : ∀ n, AEStronglyMeasurable (ψ n) μ)
    (hmx : ∀ j n, AEStronglyMeasurable (ψx j n) μ)
    {Ct C : ℝ} {Cx : ι → ℝ}
    (hbt : ∀ n, ∀ᵐ x ∂μ, ‖ψt n x‖ ≤ Ct)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖ψ n x‖ ≤ C)
    (hbx : ∀ j n, ∀ᵐ x ∂μ, ‖ψx j n x‖ ≤ Cx j)
    (hlt : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => ψt n x) Filter.atTop (nhds (ψt₀ x)))
    (hl : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => ψ n x) Filter.atTop (nhds (ψ₀ x)))
    (hlx : ∀ j, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n => ψx j n x) Filter.atTop (nhds (ψx₀ j x)))
    (hw : ∀ n, (∫ x, u x * ψt n x ∂μ) =
      (∑ j, ∫ x, F j x * ψx j n x ∂μ) + ∫ x, f x * ψ n x ∂μ) :
    (∫ x, u x * ψt₀ x ∂μ) =
      (∑ j, ∫ x, F j x * ψx₀ j x ∂μ) + ∫ x, f x * ψ₀ x ∂μ := by
  have ht := holderComparison_pairing_tendsto hu hmt hbt hlt
  have hs := holderComparison_pairing_tendsto hf hm hb hl
  have hx := tendsto_finsetSum Finset.univ (fun j _ =>
    holderComparison_pairing_tendsto (hF j) (hmx j) (hbx j) (hlx j))
  exact tendsto_nhds_unique ht ((hx.add hs).congr (fun n => (hw n).symm))

/-- On a finite parameter measure, a bounded measurable test family
preserves product integrability of each L1 physical coefficient. -/
theorem holderComparison_parameter_integrable
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SFinite μ] [IsFiniteMeasure ν]
    {u : X → ℂ} (hu : Integrable u μ) {ψ : Y → X → ℂ}
    (hm : AEStronglyMeasurable (fun p : Y × X => ψ p.1 p.2) (ν.prod μ))
    {C : ℝ} (hb : ∀ᵐ p : Y × X ∂ν.prod μ, ‖ψ p.1 p.2‖ ≤ C) :
    Integrable (fun p : Y × X => u p.2 * ψ p.1 p.2) (ν.prod μ) := by
  have hi : Integrable (fun p : Y × X => u p.2) (ν.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℂ) (μ := ν)).mul_prod hu
  exact hi.mul_bdd hm hb

/-- Every spatial slice of a compact joint test is supported in the same
compact spatial projection. This provides a common parameter-independent
locality set for integrating the separated weak equations. -/
theorem holderComparison_spatial_slice_support
    {d : ℕ} {φ : Vec d × ℝ → ℝ} (hc : HasCompactSupport φ) (s : ℝ) :
    HasCompactSupport (fun x => φ (x, s)) ∧
      tsupport (fun x => φ (x, s)) ⊆ Prod.fst '' tsupport φ := by
  have hK : IsCompact (Prod.fst '' tsupport φ) := hc.image continuous_fst
  have hs : tsupport (fun x => φ (x, s)) ⊆ Prod.fst '' tsupport φ := by
    refine closure_minimal ?_ hK.isClosed
    intro x hx
    exact ⟨(x, s), subset_tsupport φ hx, rfl⟩
  exact ⟨hK.of_isClosed_subset isClosed_closure hs, hs⟩

/-- Spatial slicing preserves smoothness and the exact Frechet derivative
in the spatial direction. No temporal derivative is introduced. -/
theorem holderComparison_spatial_slice_derivative
    {d : ℕ} {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ (x, s)) ∧
      ∀ x v : Vec d, fderiv ℝ (fun y => φ (y, s)) x v =
        fderiv ℝ φ (x, s) (v, 0) := by
  refine ⟨hφ.comp (contDiff_id.prodMk contDiff_const), ?_⟩
  intro x v
  have hi := (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) s x)
  have hd := ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x hi
  change (fderiv ℝ (φ ∘ fun y : Vec d => (id y, s)) x) v = _
  rw [hd.fderiv]
  rfl

/-- A translated compact temporal kernel is an admissible endpoint-vanishing
common-event test whenever its center stays one support radius from both
endpoints. Its derivative has the sign required by temporal mollification. -/
theorem holderComparison_temporal_kernel_test
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) {ε N s : ℝ}
    (hzero : ∀ r, ε ≤ |r| → κ r = 0) (hs : ε ≤ s) (hsN : s ≤ N - ε) :
    (∀ r, HasDerivAt (fun q => κ (s - q)) (-deriv κ (s - r)) r) ∧
      Continuous (fun r => -deriv κ (s - r)) ∧
      κ (s - 0) = 0 ∧ κ (s - N) = 0 := by
  refine ⟨?_, (hκ.continuous_deriv_one.comp (continuous_const.sub continuous_id)).neg,
    hzero _ ?_, hzero _ ?_⟩
  · intro r
    have hd : HasDerivAt κ (deriv κ (s - r)) (s - r) :=
      (hκ.differentiable (by norm_num) (s - r)).hasDerivAt
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_neg, mul_one] using
      hd.comp r ((hasDerivAt_const r s).sub (hasDerivAt_id r))
  · simpa only [sub_zero] using hs.trans (le_abs_self s)
  · exact (by linarith : ε ≤ N - s).trans (by simpa only [neg_sub] using neg_le_abs (s - N))

/-- The time derivative of a joint test is the derivative of its temporal
slice, with the original product-space direction `(0,1)`. -/
theorem holderComparison_temporal_slice_derivative
    {d : ℕ} {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (x : Vec d) :
    ContDiff ℝ 1 (fun s => φ (x, s)) ∧
      ∀ s, deriv (fun r => φ (x, r)) s = fderiv ℝ φ (x, s) (0, 1) := by
  refine ⟨hφ.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  intro s
  have hi := (hasDerivAt_const s x).prodMk (hasDerivAt_id s)
  have hd := ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt s hi
  exact hd.deriv

/-- Integrating the derivative of a translated temporal kernel against a
compact test transfers that derivative to the test, with the exact sign. -/
theorem holderComparison_temporal_kernel_pairing
    {κ φ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (s : ℝ) :
    (∫ r, (-deriv κ (r - s)) * φ r) = ∫ r, κ (r - s) * deriv φ r := by
  have hk : Continuous (fun r => κ (r - s)) :=
    hκ.continuous.comp (continuous_id.sub continuous_const)
  have hkd : Continuous (fun r => deriv κ (r - s)) :=
    hκ.continuous_deriv_one.comp (continuous_id.sub continuous_const)
  have hkdφ : Integrable (fun r => deriv κ (r - s) * φ r) :=
    (hkd.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hkφd : Integrable (fun r => κ (r - s) * deriv φ r) :=
    (hk.mul hφ.continuous_deriv_one).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hkφ : Integrable (fun r => κ (r - s) * φ r) :=
    (hk.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun r => κ (r - s)) (u' := fun r => deriv κ (r - s))
    (v := φ) (v' := deriv φ) (fun r _ => ?_) (fun r _ =>
      (hφ.differentiable (by norm_num) r).hasDerivAt) hkφd hkdφ hkφ
  · simpa only [neg_mul, integral_neg] using he.symm
  · have hd : HasDerivAt κ (deriv κ (r - s)) (r - s) :=
      (hκ.differentiable (by norm_num) (r - s)).hasDerivAt
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, sub_zero, mul_one] using
      hd.comp r ((hasDerivAt_id r).sub (hasDerivAt_const r s))

/-- Temporal averaging uses the same nonnegative normalized bump as the
standard convolution approximation, with the kernel-center parameter first. -/
noncomputable def holderComparisonTimeAverage {d : ℕ} (b : ContDiffBump (0 : ℝ))
    (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  ∫ r, b.normed volume (r - z.2) * φ (z.1, r)

/-- Evenness of the normalized bump identifies the parameter average with
ordinary convolution of the temporal slice. -/
theorem holderComparison_timeAverage_eq_convolution
    {d : ℕ} (b : ContDiffBump (0 : ℝ)) (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) :
    holderComparisonTimeAverage b φ z =
      (b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun r => φ (z.1, r)) z.2 := by
  rw [MeasureTheory.convolution_eq_swap]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    change b.normed volume (r - z.2) * φ (z.1, r) =
      b.normed volume (z.2 - r) * φ (z.1, r)
    rw [← neg_sub z.2 r, b.normed_neg]

/-- Uniform bounds of a joint test are preserved by temporal averaging. -/
theorem holderComparison_timeAverage_bound
    {d : ℕ} (b : ContDiffBump (0 : ℝ)) {φ : Vec d × ℝ → ℝ} {C : ℝ}
    (hb : ∀ z, |φ z| ≤ C) (z : Vec d × ℝ) :
    |holderComparisonTimeAverage b φ z| ≤ C := by
  rw [holderComparison_timeAverage_eq_convolution]
  exact ParabolicBridge.abs_convolution_normed_le b volume (fun r => hb (z.1, r)) z.2

/-- Shrinking temporal bumps converge at every point of a continuous joint
test. The same lemma applies to each continuous test derivative. -/
theorem holderComparison_timeAverage_tendsto
    {d : ℕ} {b : ℕ → ContDiffBump (0 : ℝ)}
    (hb : Filter.Tendsto (fun n => (b n).rOut) Filter.atTop (nhds 0))
    {φ : Vec d × ℝ → ℝ} (hφ : Continuous φ) (z : Vec d × ℝ) :
    Filter.Tendsto (fun n => holderComparisonTimeAverage (b n) φ z)
      Filter.atTop (nhds (φ z)) := by
  simp only [holderComparison_timeAverage_eq_convolution]
  exact ContDiffBump.convolution_tendsto_right_of_continuous hb
    (hφ.comp (continuous_const.prodMk continuous_id)) z.2

/-- The time average is a continuous joint test: compact support of the
original test gives one compact parameter set for every spacetime point. -/
theorem holderComparison_timeAverage_continuous
    {d : ℕ} (b : ContDiffBump (0 : ℝ)) {φ : Vec d × ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Continuous (holderComparisonTimeAverage b φ) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (hc.image continuous_snd)
  · exact (((b.continuous_normed (μ := volume)).comp
      (continuous_snd.sub continuous_fst.snd)).mul
      (hφ.comp (continuous_fst.fst.prodMk continuous_snd))).continuousOn
  · intro p r _ hr
    have hz : φ (p.1, r) = 0 := by
      by_contra hn
      exact hr ⟨(p.1, r), subset_tsupport φ hn, rfl⟩
    simp only [hz, mul_zero]

/-- The time-derivative test produced by parameter integration is precisely
the time average of the original temporal derivative. -/
theorem holderComparison_timeAverage_derivative_pairing
    {d : ℕ} (b : ContDiffBump (0 : ℝ)) {φ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (z : Vec d × ℝ) :
    (∫ r, (-deriv (b.normed volume) (r - z.2)) * φ (z.1, r)) =
      holderComparisonTimeAverage b (fun q => fderiv ℝ φ q (0, 1)) z := by
  have hs := holderComparison_temporal_slice_derivative hφ z.1
  rw [holderComparison_temporal_kernel_pairing (b.contDiff_normed : ContDiff ℝ 1 (b.normed volume))
    hs.1 (ParabolicBridge.hasCompactSupport_slice φ hc z.1)]
  unfold holderComparisonTimeAverage
  exact integral_congr_ae (Filter.Eventually.of_forall fun r => by simp only [hs.2])

/-- The temporal approximation converges in every complex pairing with an
L1 physical field, for an arbitrary local spacetime measure. -/
theorem holderComparison_timeAverage_pairing_tendsto
    {d : ℕ} {ν : Measure (Vec d × ℝ)} {u : Vec d × ℝ → ℂ}
    (hu : Integrable u ν) {b : ℕ → ContDiffBump (0 : ℝ)}
    (hb : Filter.Tendsto (fun n => (b n).rOut) Filter.atTop (nhds 0))
    {φ : Vec d × ℝ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Filter.Tendsto (fun n => ∫ z, u z * (holderComparisonTimeAverage (b n) φ z : ℂ) ∂ν)
      Filter.atTop (nhds (∫ z, u z * (φ z : ℂ) ∂ν)) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
  apply holderComparison_pairing_tendsto hu (C := C)
  · intro n
    exact (Complex.continuous_ofReal.comp
      (holderComparison_timeAverage_continuous (b n) hφ hc)).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        holderComparison_timeAverage_bound (b n) (fun q => by simpa using hC q) z
  · exact Filter.Eventually.of_forall fun z =>
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (holderComparison_timeAverage_tendsto hb hφ z)

/-- A weak equation established for temporal averages of a compact C1 joint
test passes to that test, including every prescribed derivative direction.
Only the physical coefficient fields carry integrability hypotheses. -/
theorem holderComparison_joint_weak_equation_of_timeAverages
    {d : ℕ} {ν : Measure (Vec d × ℝ)} {ι : Type*} [Fintype ι]
    {u f : Vec d × ℝ → ℂ} {F : ι → Vec d × ℝ → ℂ}
    (hu : Integrable u ν) (hf : Integrable f ν) (hF : ∀ j, Integrable (F j) ν)
    {b : ℕ → ContDiffBump (0 : ℝ)}
    (hb : Filter.Tendsto (fun n => (b n).rOut) Filter.atTop (nhds 0))
    {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (vt : Vec d × ℝ) (vx : ι → Vec d × ℝ)
    (hw : ∀ n,
      (∫ z, u z * (holderComparisonTimeAverage (b n)
        (fun q => fderiv ℝ φ q vt) z : ℂ) ∂ν) =
      (∑ j, ∫ z, F j z * (holderComparisonTimeAverage (b n)
        (fun q => fderiv ℝ φ q (vx j)) z : ℂ) ∂ν) +
      ∫ z, f z * (holderComparisonTimeAverage (b n) φ z : ℂ) ∂ν) :
    (∫ z, u z * (fderiv ℝ φ z vt : ℂ) ∂ν) =
      (∑ j, ∫ z, F j z * (fderiv ℝ φ z (vx j) : ℂ) ∂ν) +
      ∫ z, f z * (φ z : ℂ) ∂ν := by
  have hd (v : Vec d × ℝ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc (v : Vec d × ℝ) : HasCompactSupport (fun z => fderiv ℝ φ z v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : (Vec d × ℝ) →L[ℝ] ℝ => L v) (by simp)
  have ht := holderComparison_timeAverage_pairing_tendsto hu hb (hd vt) (hdc vt)
  have hs := holderComparison_timeAverage_pairing_tendsto hf hb hφ.continuous hc
  have hx := tendsto_finsetSum Finset.univ (fun j _ =>
    holderComparison_timeAverage_pairing_tendsto (hF j) hb (hd (vx j)) (hdc (vx j)))
  exact tendsto_nhds_unique ht ((hx.add hs).congr (fun n => (hw n).symm))

/-- Bounded temporal kernels paired with a continuous compact joint test
are product-integrable against any L1 physical coefficient and a compact
set of kernel centers. This discharges the Fubini hypotheses internally. -/
theorem holderComparison_kernel_weight_integrable
    {d : ℕ} {ν : Measure (Vec d × ℝ)} [SFinite ν]
    {u : Vec d × ℝ → ℂ} (hu : Integrable u ν)
    {κ : ℝ → ℝ} (hκ : Continuous κ) {B : ℝ} (hB : ∀ r, |κ r| ≤ B)
    {φ : Vec d × ℝ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {S : Set ℝ} (hS : IsCompact S) :
    Integrable (fun p : ℝ × (Vec d × ℝ) =>
      u p.2 * ((κ (p.1 - p.2.2) * φ (p.2.1, p.1) : ℝ) : ℂ))
      ((volume.restrict S).prod ν) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
  apply holderComparison_parameter_integrable hu
    (ψ := fun r z => ((κ (r - z.2) * φ (z.1, r) : ℝ) : ℂ)) (C := B * C)
  · exact (Complex.continuous_ofReal.comp
      ((hκ.comp (continuous_fst.sub continuous_snd.snd)).mul
        (hφ.comp (continuous_snd.fst.prodMk continuous_fst)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB _) (by simpa only [Real.norm_eq_abs] using hC _)
        (abs_nonneg _) ((abs_nonneg (κ 0)).trans (hB 0))

/-- Restricting kernel centers to a set containing the temporal support
preserves the entire complex-valued parameter pairing. -/
theorem holderComparison_kernel_pairing_restrict
    {d : ℕ} {φ : Vec d × ℝ → ℝ} {S : Set ℝ}
    (hs : tsupport φ ⊆ Set.univ ×ˢ S) (κ : ℝ → ℝ) (z : Vec d × ℝ) :
    (∫ r in S, ((κ (r - z.2) * φ (z.1, r) : ℝ) : ℂ)) =
      ((∫ r, κ (r - z.2) * φ (z.1, r) : ℝ) : ℂ) := by
  rw [integral_complex_ofReal]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  have hz : φ (z.1, r) = 0 := by
    by_contra hn
    exact hr (hs (subset_tsupport φ hn)).2
  rw [hz, mul_zero]

/-- Integrating admissible separated kernel tests gives the exact weak
identity for a time average of the joint test. Derivatives of the kernel
are transferred to the original temporal derivative by integration by parts. -/
theorem holderComparison_timeAverage_weak_equation
    {d : ℕ} {ν : Measure (Vec d × ℝ)} [SFinite ν]
    {ι : Type*} [Fintype ι] {u f : Vec d × ℝ → ℂ} {F : ι → Vec d × ℝ → ℂ}
    (hu : Integrable u ν) (hf : Integrable f ν) (hF : ∀ j, Integrable (F j) ν)
    (b : ContDiffBump (0 : ℝ))
    {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    {S : Set ℝ} (hS : IsCompact S) (hs : tsupport φ ⊆ Set.univ ×ˢ S)
    (vx : ι → Vec d)
    (hw : ∀ r ∈ S,
      (∫ z, u z * (((-deriv (b.normed volume) (r - z.2)) * φ (z.1, r) : ℝ) : ℂ) ∂ν) =
      (∑ j, ∫ z, F j z * ((b.normed volume (r - z.2) *
        fderiv ℝ φ (z.1, r) (vx j, 0) : ℝ) : ℂ) ∂ν) +
      ∫ z, f z * ((b.normed volume (r - z.2) * φ (z.1, r) : ℝ) : ℂ) ∂ν) :
    (∫ z, u z * (holderComparisonTimeAverage b
      (fun q => fderiv ℝ φ q (0, 1)) z : ℂ) ∂ν) =
    (∑ j, ∫ z, F j z * (holderComparisonTimeAverage b
      (fun q => fderiv ℝ φ q (vx j, 0)) z : ℂ) ∂ν) +
    ∫ z, f z * (holderComparisonTimeAverage b φ z : ℂ) ∂ν := by
  let κ : ℝ → ℝ := b.normed volume
  have hκ : ContDiff ℝ 1 κ := b.contDiff_normed
  have hκc : HasCompactSupport κ := b.hasCompactSupport_normed
  obtain ⟨B, hB⟩ := hκ.continuous.bounded_above_of_compact_support hκc
  obtain ⟨D, hD⟩ := hκ.continuous_deriv_one.neg.bounded_above_of_compact_support hκc.deriv.neg
  have hd (v : Vec d × ℝ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc (v : Vec d × ℝ) : HasCompactSupport (fun z => fderiv ℝ φ z v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : (Vec d × ℝ) →L[ℝ] ℝ => L v) (by simp)
  have hit := holderComparison_kernel_weight_integrable hu hκ.continuous_deriv_one.neg
    (fun r => by simpa only [Real.norm_eq_abs] using hD r) hφ.continuous hc hS
  have hix (j : ι) := holderComparison_kernel_weight_integrable (hF j) hκ.continuous
    (fun r => by simpa only [Real.norm_eq_abs] using hB r) (hd (vx j, 0)) (hdc (vx j, 0)) hS
  have hi := holderComparison_kernel_weight_integrable hf hκ.continuous
    (fun r => by simpa only [Real.norm_eq_abs] using hB r) hφ.continuous hc hS
  have he := holderComparison_parameter_weak_equation u f F
    (fun r z => (((-deriv κ (r - z.2)) * φ (z.1, r) : ℝ) : ℂ))
    (fun r z => ((κ (r - z.2) * φ (z.1, r) : ℝ) : ℂ))
    (fun j r z => ((κ (r - z.2) * fderiv ℝ φ (z.1, r) (vx j, 0) : ℝ) : ℂ))
    hit hix hi ((ae_restrict_mem hS.measurableSet).mono fun r hr => hw r hr)
  have hsp (v : Vec d × ℝ) : tsupport (fun q => fderiv ℝ φ q v) ⊆ Set.univ ×ˢ S :=
    (tsupport_fderiv_apply_subset ℝ v).trans hs
  have ht (z : Vec d × ℝ) :
      (∫ r in S, (((-deriv κ (r - z.2)) * φ (z.1, r) : ℝ) : ℂ)) =
        (holderComparisonTimeAverage b (fun q => fderiv ℝ φ q (0, 1)) z : ℂ) := by
    rw [holderComparison_kernel_pairing_restrict hs (fun r => -deriv κ r) z]
    exact congrArg Complex.ofReal (holderComparison_timeAverage_derivative_pairing b hφ hc z)
  have hx (j : ι) (z : Vec d × ℝ) :
      (∫ r in S, ((κ (r - z.2) * fderiv ℝ φ (z.1, r) (vx j, 0) : ℝ) : ℂ)) =
        (holderComparisonTimeAverage b (fun q => fderiv ℝ φ q (vx j, 0)) z : ℂ) :=
    holderComparison_kernel_pairing_restrict (hsp (vx j, 0)) κ z
  have hv (z : Vec d × ℝ) :
      (∫ r in S, ((κ (r - z.2) * φ (z.1, r) : ℝ) : ℂ)) =
        (holderComparisonTimeAverage b φ z : ℂ) :=
    holderComparison_kernel_pairing_restrict hs κ z
  simpa only [ht, hx, hv] using he

/-- Endpoint-vanishing separated tests determine the weak equation for every
smooth compact joint test supported a positive distance from the endpoints.
The temporal approximation and all product-integrability conditions are
constructed from the original coefficient fields. -/
theorem holderComparison_joint_weak_equation_of_separated
    {d : ℕ} {ν : Measure (Vec d × ℝ)} [SFinite ν]
    {ι : Type*} [Fintype ι] {u f : Vec d × ℝ → ℂ} {F : ι → Vec d × ℝ → ℂ}
    (hu : Integrable u ν) (hf : Integrable f ν) (hF : ∀ j, Integrable (F j) ν)
    {N δ : ℝ} (hδ : 0 < δ) (vx : ι → Vec d)
    {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Set.univ ×ˢ Set.Icc δ (N - δ))
    (hw : ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
      η 0 = 0 → η N = 0 →
      ∀ (ψ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Prod.fst '' tsupport φ →
      (∫ z, u z * ((η' z.2 * ψ z.1 : ℝ) : ℂ) ∂ν) =
      (∑ j, ∫ z, F j z * ((η z.2 * fderiv ℝ ψ z.1 (vx j) : ℝ) : ℂ) ∂ν) +
      ∫ z, f z * ((η z.2 * ψ z.1 : ℝ) : ℂ) ∂ν) :
    (∫ z, u z * (fderiv ℝ φ z (0, 1) : ℂ) ∂ν) =
      (∑ j, ∫ z, F j z * (fderiv ℝ φ z (vx j, 0) : ℂ) ∂ν) +
      ∫ z, f z * (φ z : ℂ) ∂ν := by
  let b : ℕ → ContDiffBump (0 : ℝ) := ParabolicBridge.shrinkBump δ hδ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  apply holderComparison_joint_weak_equation_of_timeAverages hu hf hF
    (ParabolicBridge.shrinkBump_tendsto δ hδ) hφ1 hc (0, 1) (fun j => (vx j, 0))
  intro n
  apply holderComparison_timeAverage_weak_equation hu hf hF (b n) hφ1 hc
    isCompact_Icc hs vx
  intro r hr
  have hbδ : (b n).rOut ≤ δ := by
    change δ / ((n : ℝ) + 2) ≤ δ
    exact div_le_self hδ.le (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hz (q : ℝ) (hq : (b n).rOut ≤ |q|) : (b n).normed volume q = 0 := by
    by_contra hn
    have hm : q ∈ Function.support ((b n).normed volume) := hn
    rw [(b n).support_normed_eq] at hm
    exact (not_lt_of_ge hq) (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hm)
  obtain ⟨hη, hη', hη0, hηN⟩ := holderComparison_temporal_kernel_test
    (N := N) (b n).contDiff_normed hz (hbδ.trans hr.1) (by linarith [hr.2])
  obtain ⟨hψ, hψd⟩ := holderComparison_spatial_slice_derivative hφ r
  simpa only [hψd] using hw
    (fun s => (b n).normed volume (r - s))
    (fun s => -deriv ((b n).normed volume) (r - s)) hη hη' hη0 hηN
    (fun x => φ (x, r)) hψ (holderComparison_spatial_slice_support hc r).1
    (holderComparison_spatial_slice_support hc r).2

/-- A compact joint test supported in an open time slab has a positive
uniform margin from both endpoints. The margin is derived from support,
rather than imposed as an extra admissibility condition. -/
theorem holderComparison_temporal_support_margin
    {d : ℕ} {N : ℝ} {φ : Vec d × ℝ → ℝ} (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Set.univ ×ˢ Set.Ioo 0 N) :
    ∃ δ : ℝ, 0 < δ ∧ tsupport φ ⊆ Set.univ ×ˢ Set.Icc δ (N - δ) := by
  by_cases he : (tsupport φ).Nonempty
  · have hcont : Continuous (fun z : Vec d × ℝ => min z.2 (N - z.2)) :=
      continuous_snd.min (continuous_const.sub continuous_snd)
    obtain ⟨z, hz, hm⟩ := hc.exists_isMinOn he hcont.continuousOn
    refine ⟨min z.2 (N - z.2), lt_min (hs hz).2.1 (sub_pos.mpr (hs hz).2.2), ?_⟩
    intro q hq
    have h : min z.2 (N - z.2) ≤ min q.2 (N - q.2) := hm hq
    exact ⟨Set.mem_univ _, h.trans (min_le_left _ _),
      by have ht := h.trans (min_le_right _ _); linarith⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro z hz
    exact (he ⟨z, hz⟩).elim

/-- Multiplication by a continuous physical coefficient preserves local L1
on a compact spatial set and a compact time interval. -/
theorem holderComparison_local_mul_integrable
    {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K) {s T : ℝ}
    {u g : Vec d × ℝ → ℂ}
    (hu : Integrable u ((volume.restrict K).prod (volume.restrict (Set.Icc s T))))
    (hg : Continuous g) :
    Integrable (fun z => u z * g z)
      ((volume.restrict K).prod (volume.restrict (Set.Icc s T))) := by
  rw [Measure.prod_restrict] at hu ⊢
  exact IntegrableOn.mul_continuousOn hu hg.continuousOn (hK.prod isCompact_Icc)

/-- The actual nested spatial/time pairing equals its local product integral
when its spatial multiplier is supported in the chosen compact set. -/
theorem holderComparison_local_separated_pairing
    {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K) {s T : ℝ}
    {u : Vec d × ℝ → ℂ}
    (hu : Integrable u ((volume.restrict K).prod (volume.restrict (Set.Icc s T))))
    {ψ : Vec d → ℂ} (hψ : Continuous ψ) (hs : tsupport ψ ⊆ K)
    {η : ℝ → ℝ} (hη : Continuous η) :
    (∫ x, (∫ r in Set.Icc s T, (η r : ℂ) * u (x, r)) * ψ x) =
      ∫ z, u z * ((η z.2 : ℂ) * ψ z.1)
        ∂((volume.restrict K).prod (volume.restrict (Set.Icc s T))) := by
  have hi := holderComparison_local_mul_integrable hK hu
    ((Complex.continuous_ofReal.comp (hη.comp continuous_snd)).mul (hψ.comp continuous_fst))
  have he (x : Vec d) :
      (∫ r in Set.Icc s T, (η r : ℂ) * u (x, r)) * ψ x =
      ∫ r in Set.Icc s T, u (x, r) * ((η r : ℂ) * ψ x) := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by ring
  calc
    _ = ∫ x in K, (∫ r in Set.Icc s T, (η r : ℂ) * u (x, r)) * ψ x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
    _ = ∫ x in K, ∫ r in Set.Icc s T, u (x, r) * ((η r : ℂ) * ψ x) := by
      simp only [he]
    _ = _ := (integral_prod _ hi).symm

/-- Compact spatial support gives genuine outer integrability of the nested
pairing, as required when a finite spatial flux sum is integrated. -/
theorem holderComparison_local_pairing_integrable
    {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K) {s T : ℝ}
    {u : Vec d × ℝ → ℂ}
    (hu : Integrable u ((volume.restrict K).prod (volume.restrict (Set.Icc s T))))
    {ψ : Vec d → ℂ} (hψ : Continuous ψ) (hs : tsupport ψ ⊆ K)
    {η : ℝ → ℝ} (hη : Continuous η) :
    Integrable (fun x => (∫ r in Set.Icc s T, (η r : ℂ) * u (x, r)) * ψ x) := by
  have hi := holderComparison_local_mul_integrable hK hu
    ((Complex.continuous_ofReal.comp (hη.comp continuous_snd)).mul (hψ.comp continuous_fst))
  have he (x : Vec d) :
      (∫ r in Set.Icc s T, u (x, r) * ((η r : ℂ) * ψ x)) =
      (∫ r in Set.Icc s T, (η r : ℂ) * u (x, r)) * ψ x := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by ring
  have hl : IntegrableOn
      (fun x => (∫ r in Set.Icc s T, (η r : ℂ) * u (x, r)) * ψ x) K volume := by
    change Integrable _ (volume.restrict K)
    simpa only [Function.comp_apply, Pi.mul_apply, he] using hi.integral_prod_left
  have hz : K.indicator
      (fun x => (∫ r in Set.Icc s T, (η r : ℂ) * u (x, r)) * ψ x) =
      (fun x => (∫ r in Set.Icc s T, (η r : ℂ) * u (x, r)) * ψ x) := by
    funext x
    by_cases hx : x ∈ K
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  rwa [← integrable_indicator_iff hK.measurableSet, hz] at hl

/-- The actual time-integrated matrix row can be moved inside the local
product pairing. Only local L1 of its gradient coordinates is used. -/
theorem holderComparison_local_flux_pairing
    {d : ℕ} {ι : Type*} [Fintype ι] {K : Set (Vec d)} (hK : IsCompact K) {s T : ℝ}
    {u : ι → Vec d × ℝ → ℂ}
    (hu : ∀ j, Integrable (u j) ((volume.restrict K).prod (volume.restrict (Set.Icc s T))))
    (a : ι → Vec d → ℂ) (ha : ∀ j, Continuous (a j))
    {ψ : Vec d → ℂ} (hψ : Continuous ψ) (hs : tsupport ψ ⊆ K)
    {η : ℝ → ℝ} (hη : Continuous η) :
    (∫ x, (∑ j, a j x * (∫ r in Set.Icc s T, (η r : ℂ) * u j (x, r))) * ψ x) =
      ∫ z, (∑ j, a j z.1 * u j z) * ((η z.2 : ℂ) * ψ z.1)
        ∂((volume.restrict K).prod (volume.restrict (Set.Icc s T))) := by
  have hG : Integrable (fun z => ∑ j, a j z.1 * u j z)
      ((volume.restrict K).prod (volume.restrict (Set.Icc s T))) := by
    apply integrable_finsetSum
    intro j _
    simpa only [Function.comp_apply, mul_comm] using holderComparison_local_mul_integrable hK (hu j)
      ((ha j).comp continuous_fst)
  rw [← holderComparison_local_separated_pairing hK hG hψ hs hη]
  have hr (j : ι) := holderComparison_local_mul_integrable hK (hu j)
    (Complex.continuous_ofReal.comp (hη.comp continuous_snd))
  have he : ∀ᵐ x ∂volume.restrict K,
      (∫ r in Set.Icc s T, (η r : ℂ) * (∑ j, a j x * u j (x, r))) =
      ∑ j, a j x * (∫ r in Set.Icc s T, (η r : ℂ) * u j (x, r)) := by
    filter_upwards [ae_all_iff.mpr (fun j => (hr j).prod_right_ae)] with x hx
    have hi j : Integrable (fun r => (η r : ℂ) * u j (x, r))
        (volume.restrict (Set.Icc s T)) := by
      simpa only [Function.comp_apply, mul_comm] using hx j
    calc
      _ = ∫ r in Set.Icc s T, ∑ j, a j x * ((η r : ℂ) * u j (x, r)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun r => by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = _ := by
        rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
        simp only [integral_const_mul]
  have hlocal : (∫ x in K,
      (∑ j, a j x * (∫ r in Set.Icc s T, (η r : ℂ) * u j (x, r))) * ψ x) =
      ∫ x in K, (∫ r in Set.Icc s T,
        (η r : ℂ) * (∑ j, a j x * u j (x, r))) * ψ x :=
    integral_congr_ae (he.mono fun x hx => congrArg (fun z => z * ψ x) hx.symm)
  have hrestrict (G : Vec d → ℂ) : (∫ x in K, G x * ψ x) = ∫ x, G x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  simpa only [hrestrict] using hlocal

/-- A time-integrated matrix row has an integrable spatial pairing, so
finite row sums may be split before converting them to product integrals. -/
theorem holderComparison_local_flux_pairing_integrable
    {d : ℕ} {ι : Type*} [Fintype ι] {K : Set (Vec d)} (hK : IsCompact K) {s T : ℝ}
    {u : ι → Vec d × ℝ → ℂ}
    (hu : ∀ j, Integrable (u j) ((volume.restrict K).prod (volume.restrict (Set.Icc s T))))
    (a : ι → Vec d → ℂ) (ha : ∀ j, Continuous (a j))
    {ψ : Vec d → ℂ} (hψ : Continuous ψ) (hs : tsupport ψ ⊆ K)
    {η : ℝ → ℝ} (hη : Continuous η) :
    Integrable (fun x => (∑ j, a j x *
      (∫ r in Set.Icc s T, (η r : ℂ) * u j (x, r))) * ψ x) := by
  have hi (j : ι) := holderComparison_local_pairing_integrable hK (hu j)
    ((ha j).mul hψ) ((tsupport_mul_subset_right (f := a j) (g := ψ)).trans hs) hη
  have he : (fun x => (∑ j, a j x *
      (∫ r in Set.Icc s T, (η r : ℂ) * u j (x, r))) * ψ x) =
      (fun x => ∑ j, (∫ r in Set.Icc s T, (η r : ℂ) * u j (x, r)) *
        (a j x * ψ x)) := by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j _ => hi j)

/-- Squared integrability of an L2-valued path passes to its single joint
representative, with the actual L2 norm giving the section integral. -/
theorem holderComparison_integrable_sq_joint_l2_representative {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure T} {u : T → Lp ℂ 2 μ}
    (hu : Integrable (fun t => ‖u t‖ ^ 2) ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    Integrable (fun p => ‖U p‖ ^ 2) (ν.prod μ) := by
  apply (integrable_prod_iff (hU.norm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).norm.integrable_sq).congr
    ((heq t).symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)), ?_⟩
  apply hu.congr
  filter_upwards with t
  have hn : ‖u t‖ ^ 2 = ∫ ω, ‖(u t) ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hn]
  apply integral_congr_ae
  filter_upwards [heq t] with ω hω
  simp only [hω, Real.norm_eq_abs]
  exact (abs_of_nonneg (sq_nonneg ‖(u t) ω‖)).symm

open EinsteinRelation in
/-- The existing stationary spacetime transport applied to the squared norm
produces local L2 on one event before every compact spatial region. -/
theorem holderComparison_ae_locally_memLp_joint_spatial_translate {T : Type*} [MeasurableSpace T]
    {ν : Measure T} [SFinite ν] {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {U : T × FieldPair d → ℂ} (hU : Measurable U)
    (hi : Integrable (fun p => ‖U p‖ ^ 2) (ν.prod Q)) :
    ∀ᵐ ω ∂Q, ∀ K : Set (PDE.Vec d), IsCompact K →
      MemLp (fun p : PDE.Vec d × T => U (p.2, translate p.1 ω)) 2
        ((volume.restrict K).prod ν) := by
  have hc : Integrable (fun p => ((‖U p‖ ^ 2 : ℝ) : ℂ)) (ν.prod Q) :=
    by simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hi
  filter_upwards [ae_locally_integrable_joint_spatial_translate Q hQ hc] with ω hω
  intro K hK
  have hm : Measurable (fun p : PDE.Vec d × T => U (p.2, translate p.1 ω)) :=
    hU.comp (measurable_snd.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_fst.prodMk measurable_const)))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using! Complex.reCLM.integrable_comp (hω K hK)


/-- Local spacetime L2 gives one time event before every compact spatial set,
by first taking sections on a countable exhaustion by closed balls. -/
theorem holderComparison_ae_slices_memLp {T : Type*} [MeasurableSpace T]
    {ν : Measure T} [SFinite ν] {d : ℕ}
    {u : Vec d × T → ℂ} (hu : Measurable u)
    (hloc : ∀ K : Set (Vec d), IsCompact K →
      MemLp u 2 ((volume.restrict K).prod ν)) :
    ∀ᵐ s ∂ν, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => u (x, s)) 2 (volume.restrict K) := by
  have hn (n : ℕ) : ∀ᵐ s ∂ν,
      MemLp (fun x => u (x, s)) 2
        (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) := by
    have hi := ((hloc (Metric.closedBall (0 : Vec d) (n : ℝ))
      (isCompact_closedBall _ _)).norm.integrable_sq).prod_left_ae
    filter_upwards [hi] with s hs
    exact (memLp_two_iff_integrable_sq_norm
      (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hs
  filter_upwards [ae_all_iff.mpr hn] with s hs
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Vec d)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hKn : K ⊆ Metric.closedBall (0 : Vec d) (n : ℝ) :=
    hr.trans ((Metric.ball_subset_ball hn.le).trans Metric.ball_subset_closedBall)
  exact (hs n).mono_measure (Measure.restrict_mono_set volume hKn)


/-- Local square integrability is a measurable parameter predicate. The
uncountable compact-set formulation is reduced to closed balls. -/
theorem holderComparison_measurableSet_locally_memLp {A : Type*}
    [MeasurableSpace A] {d : ℕ} {u : A × Vec d → ℂ} (hu : Measurable u) :
    MeasurableSet {a | ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => u (a, x)) 2 (volume.restrict K)} := by
  have hm (K : Set (Vec d)) : MeasurableSet {a |
      MemLp (fun x => u (a, x)) 2 (volume.restrict K)} := by
    have hi : Measurable (fun a => ∫⁻ x, ENNReal.ofReal ‖‖u (a, x)‖ ^ 2‖
        ∂volume.restrict K) :=
      ((hu.norm.pow_const 2).norm.ennreal_ofReal).lintegral_prod_right'
    have hset : MeasurableSet {a | (∫⁻ x, ENNReal.ofReal ‖‖u (a, x)‖ ^ 2‖
        ∂volume.restrict K) < (∞ : ℝ≥0∞)} := measurableSet_lt hi measurable_const
    convert hset using 1
    ext a
    have hsec : Measurable (fun x => u (a, x)) :=
      hu.comp (measurable_const.prodMk measurable_id)
    change MemLp (fun x => u (a, x)) 2 (volume.restrict K) ↔ _
    rw [memLp_two_iff_integrable_sq_norm hsec.aestronglyMeasurable]
    exact (and_iff_right (hsec.norm.pow_const 2).aestronglyMeasurable).trans
      (hasFiniteIntegral_iff_norm _)
  have he : {a | ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => u (a, x)) 2 (volume.restrict K)} =
      {a | ∀ n : ℕ, MemLp (fun x => u (a, x)) 2
        (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ)))} := by
    ext a
    constructor
    · exact fun h n => h _ (isCompact_closedBall _ _)
    · intro h K hK
      obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Vec d)
      obtain ⟨n, hn⟩ := exists_nat_gt r
      exact (h n).mono_measure (Measure.restrict_mono_set volume
        (hr.trans ((Metric.ball_subset_ball hn.le).trans Metric.ball_subset_closedBall)))
  rw [he]
  simpa only [Set.ofPred_forall] using MeasurableSet.iInter (fun n : ℕ => hm
    (Metric.closedBall (0 : Vec d) (n : ℝ)))


/-- A compact continuous spatial multiplier pairs integrably with a locally
square-integrable field, with no global integrability premise. -/
theorem holderComparison_local_spatial_mul_integrable {d : ℕ}
    {u : Vec d → ℂ}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => u x * (ψ x : ℂ)) := by
  have huK : MemLp ((tsupport ψ).indicator u) 2 volume :=
    (memLp_indicator_iff_restrict hc.isCompact.measurableSet).mpr (hu _ hc.isCompact)
  have hp : MemLp (fun x => (ψ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hψ).memLp_of_hasCompactSupport
      (hc.comp_left (by simp))
  apply (huK.integrable_mul hp).congr
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ tsupport ψ
    · simp only [Pi.mul_apply, Set.indicator_of_mem hx]
    · simp only [Pi.mul_apply, Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
        Complex.ofReal_zero, mul_zero]

/-- Spatial pairings of a measurable family are measurable in the parameter,
including when some sections are not integrable. -/
theorem holderComparison_measurable_spatial_pairing {A : Type*}
    [MeasurableSpace A] {d : ℕ} {u : A × Vec d → ℂ} (hu : Measurable u)
    {ψ : Vec d → ℝ} (hψ : Measurable ψ) :
    Measurable (fun a => ∫ x, u (a, x) * (ψ x : ℂ)) :=
  (hu.mul (Complex.continuous_ofReal.measurable.comp
    (hψ.comp measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable


/-- Local L2 and the fixed-test weak-gradient identities give one event
before every coordinate and every smooth compact spatial test. -/
theorem holderComparison_ae_all_spatial_gradients {A : Type*}
    [MeasurableSpace A] {d : ℕ} (μ : Measure A)
    (u : A → Vec d → ℂ) (g : A → Fin d → Vec d → ℂ)
    (hloc : ∀ᵐ a ∂μ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (u a) 2 (volume.restrict K) ∧
      ∀ j, MemLp (g a j) 2 (volume.restrict K))
    (hfixed : ∀ j (ψ : Vec d → ℝ), EinsteinRelation.IsSpatialTest Set.univ ψ →
      ∀ᵐ a ∂μ, (∫ x, u a x * (EinsteinRelation.coordinateDerivative j ψ x : ℂ)) =
        -(∫ x, g a j x * (ψ x : ℂ))) :
    ∀ᵐ a ∂μ, ∀ j (ψ : Vec d → ℝ), EinsteinRelation.IsSpatialTest Set.univ ψ →
      (∫ x, u a x * (EinsteinRelation.coordinateDerivative j ψ x : ℂ)) =
        -(∫ x, g a j x * (ψ x : ℂ)) := by
  have hall (j : Fin d) := ae_all_spatial_tests_of_ae_fixed_test μ
    (fun a x => g a j x) (fun a k x => if k = j then u a x else 0)
    (by
      filter_upwards [hloc] with a ha
      intro K hK
      refine ⟨(ha K hK).2 j, ?_⟩
      intro k
      by_cases hk : k = j
      · simpa only [hk, ite_true] using (ha K hK).1
      · simp only [hk, ite_false]
        exact MemLp.zero')
    (by
      intro ψ hψ hc
      filter_upwards [hloc, hfixed j ψ ⟨hψ, hc, Set.subset_univ _⟩] with a ha he
      have hd : Continuous (EinsteinRelation.coordinateDerivative j ψ) :=
        ((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).continuous
      have hiu := holderComparison_local_spatial_mul_integrable
        (fun K hK => (ha K hK).1) hd (by simpa only [EinsteinRelation.coordinateDerivative] using!
          (hc.fderiv_apply ℝ (EinsteinRelation.unitVector j)))
      have hig := holderComparison_local_spatial_mul_integrable
        (fun K hK => (ha K hK).2 j) hψ.continuous hc
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [integral_add hig hiu, he, add_neg_cancel])
  filter_upwards [hloc, ae_all_iff.mpr hall] with a ha he
  intro j ψ hψ
  have hd : Continuous (EinsteinRelation.coordinateDerivative j ψ) :=
    ((contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const).continuous
  have hiu := holderComparison_local_spatial_mul_integrable
    (fun K hK => (ha K hK).1) hd (by simpa only [EinsteinRelation.coordinateDerivative] using!
      (hψ.2.1.fderiv_apply ℝ (EinsteinRelation.unitVector j)))
  have hig := holderComparison_local_spatial_mul_integrable
    (fun K hK => (ha K hK).2 j) hψ.1.continuous hψ.2.1
  have hz := he j ψ hψ.1 hψ.2.1
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hz
  rw [integral_add hig hiu, add_comm] at hz
  exact eq_neg_of_add_eq_zero_left hz


/-- A continuous joint multiplier with compact spatial locality gives the
spatial-first product pairing by integrating its spatial slices in time. -/
theorem holderComparison_local_joint_pairing {d : ℕ} {K : Set (Vec d)}
    (hK : IsCompact K) {b c : ℝ} {u q : Vec d × ℝ → ℂ}
    (hu : Integrable u ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hq : Continuous q) (hs : ∀ z, z.1 ∉ K → q z = 0) :
    (∫ s in Icc b c, ∫ x, u (x, s) * q (x, s)) =
      ∫ z, u z * q z ∂((volume.restrict K).prod (volume.restrict (Icc b c))) := by
  have hi := holderComparison_local_mul_integrable hK hu hq
  calc
    _ = ∫ s in Icc b c, ∫ x in K, u (x, s) * q (x, s) := by
      apply integral_congr_ae
      exact ae_of_all _ fun s => (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hs (x, s) hx, mul_zero])).symm
    _ = _ := (integral_prod_symm _ hi).symm

/-- A common event for the spatial weak-gradient identities can be integrated
against the slices of every smooth compact joint test. -/
theorem holderComparison_joint_weak_gradient_of_spatial_slices
    {d : ℕ} {b c : ℝ} {u v : Vec d × ℝ → ℂ}
    (hu : ∀ K : Set (Vec d), IsCompact K →
      Integrable u ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hv : ∀ K : Set (Vec d), IsCompact K →
      Integrable v ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (j : Fin d)
    (hgrad : ∀ᵐ s ∂volume.restrict (Icc b c), ∀ ψ : Vec d → ℝ,
      EinsteinRelation.IsSpatialTest univ ψ →
        (∫ x, u (x, s) * (EinsteinRelation.coordinateDerivative j ψ x : ℂ)) =
          -(∫ x, v (x, s) * (ψ x : ℂ)))
    {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ z, u z * (fderiv ℝ φ z (EinsteinRelation.unitVector j, 0) : ℂ)
      ∂((volume.restrict (Prod.fst '' tsupport φ)).prod (volume.restrict (Icc b c)))) =
      -(∫ z, v z * (φ z : ℂ)
        ∂((volume.restrict (Prod.fst '' tsupport φ)).prod (volume.restrict (Icc b c)))) := by
  let K := Prod.fst '' tsupport φ
  have hK : IsCompact K := hc.image continuous_fst
  have hs z (hz : z.1 ∉ K) : z ∉ tsupport φ :=
    fun h => hz ⟨z, h, rfl⟩
  have hd : Continuous (fun z => (fderiv ℝ φ z (EinsteinRelation.unitVector j, 0) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const).continuous)
  have hid := holderComparison_local_joint_pairing hK (hu K hK) hd (by
    intro z hz
    have he : fderiv ℝ φ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hs z hz (tsupport_fderiv_subset ℝ h))
    simp only [he, zero_apply, Complex.ofReal_zero])
  have hiv := holderComparison_local_joint_pairing (q := fun z => (φ z : ℂ))
    hK (hv K hK) (Complex.continuous_ofReal.comp hφ.continuous) (by
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (hs z hz), Complex.ofReal_zero])
  rw [← hid, ← hiv, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hgrad] with s hsgrad
  have hslice := holderComparison_spatial_slice_derivative hφ s
  have he := hsgrad (fun x => φ (x, s))
    ⟨hslice.1, (holderComparison_spatial_slice_support hc s).1, Set.subset_univ _⟩
  simpa only [EinsteinRelation.coordinateDerivative, hslice.2] using he

/-- Compact continuous real multipliers pair integrably with a complex L1
field for any measure. -/
theorem holderComparison_integrable_mul_compact_real
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {u : E → ℂ} (hu : Integrable u μ)
    {q : E → ℝ} (hq : Continuous q) (hc : HasCompactSupport q) :
    Integrable (fun z => u z * (q z : ℂ)) μ := by
  obtain ⟨M, hM⟩ := hq.bounded_above_of_compact_support hc
  apply hu.mul_bdd (c := M) (Complex.continuous_ofReal.comp hq).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hM z

/-- Real linear projections commute with complex pairings against a compact
continuous real multiplier. -/
theorem holderComparison_project_pairing
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {u : E → ℂ} (hu : Integrable u μ)
    (R : ℂ →L[ℝ] ℝ) {q : E → ℝ} (hq : Continuous q) (hc : HasCompactSupport q) :
    (∫ z, R (u z) * q z ∂μ) = R (∫ z, u z * (q z : ℂ) ∂μ) := by
  rw [← R.integral_comp_comm (holderComparison_integrable_mul_compact_real hu hq hc)]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change R (u z) * q z = R (u z * (q z : ℂ))
    rw [mul_comm (u z), ← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]

/-- Complex weak identities extend from smooth tests to compact C1 tests by
applying the real extension to both real linear projections. -/
theorem holderComparison_complex_weak_identity_C1_of_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Set E} (hΩ : IsOpen Ω)
    {ι : Type*} [Fintype ι] (w : ι → E) (A : ι → E → ℂ) (B : E → ℂ)
    (hA : ∀ i, IntegrableOn (A i) Ω μ) (hB : IntegrableOn B Ω μ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∑ i, (∫ z in Ω, A i z * (fderiv ℝ φ z (w i) : ℂ) ∂μ)) +
        ∫ z in Ω, B z * (φ z : ℂ) ∂μ = 0)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    (∑ i, (∫ z in Ω, A i z * (fderiv ℝ φ z (w i) : ℂ) ∂μ)) +
      ∫ z in Ω, B z * (φ z : ℂ) ∂μ = 0 := by
  have hproj (R : ℂ →L[ℝ] ℝ) :
      (∑ i, (∫ z in Ω, R (A i z) * fderiv ℝ φ z (w i) ∂μ)) +
        ∫ z in Ω, R (B z) * φ z ∂μ = 0 := by
    apply ParabolicBridge.weak_identity_C1_of_smooth μ hΩ w
      (fun i z => R (A i z)) (fun z => R (B z))
      (fun i => R.integrable_comp (hA i)) (R.integrable_comp hB) _ φ hφ hc hs
    intro ψ hψ hcψ hsψ
    have hd i : Continuous (fun z => fderiv ℝ ψ z (w i)) :=
      ((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).continuous
    have hcd i : HasCompactSupport (fun z => fderiv ℝ ψ z (w i)) :=
      (hcψ.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L (w i)) (by simp)
    simp_rw [holderComparison_project_pairing (hA _) R (hd _) (hcd _)]
    rw [holderComparison_project_pairing hB R hψ.continuous hcψ,
      ← map_sum, ← map_add, h ψ hψ hcψ hsψ, map_zero]
  have hd i : Continuous (fun z => fderiv ℝ φ z (w i)) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcd i : HasCompactSupport (fun z => fderiv ℝ φ z (w i)) :=
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L (w i)) (by simp)
  have he (R : ℂ →L[ℝ] ℝ) : R
      ((∑ i, (∫ z in Ω, A i z * (fderiv ℝ φ z (w i) : ℂ) ∂μ)) +
        ∫ z in Ω, B z * (φ z : ℂ) ∂μ) = 0 := by
    rw [map_add, map_sum]
    simp_rw [← holderComparison_project_pairing (hA _) R (hd _) (hcd _)]
    rw [← holderComparison_project_pairing hB R hφ.continuous hc]
    exact hproj R
  exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)

/-- Pairings supported in a joint test's support agree on the support-based
product measure and on its prescribed open cylinder. -/
theorem holderComparison_joint_test_pairing_localize
    {d : ℕ} {U : Set (Vec d)} {b c : ℝ} {φ : Vec d × ℝ → ℝ}
    (hs : tsupport φ ⊆ U ×ˢ Ioo b c) {F : Vec d × ℝ → ℂ}
    (hF : ∀ z, z ∉ tsupport φ → F z = 0) :
    (∫ z, F z ∂((volume.restrict (Prod.fst '' tsupport φ)).prod
      (volume.restrict (Icc b c)))) = ∫ z in U ×ˢ Ioo b c, F z := by
  have hlocal : tsupport φ ⊆ (Prod.fst '' tsupport φ) ×ˢ Icc b c := by
    intro z hz
    exact ⟨⟨z, hz, rfl⟩, (hs hz).2.1.le, (hs hz).2.2.le⟩
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  calc
    _ = ∫ z, F z := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => hF z (fun h => hz (hlocal h)))
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => hF z (fun h => hz (hs h)))).symm

/-- Joint spatial gradient identities on smooth tests provide the compact C1
identities required by the local physical comparison theorem. -/
theorem holderComparison_joint_weak_gradient_C1
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {b c : ℝ}
    {u v : Vec d × ℝ → ℂ}
    (hu : IntegrableOn u (U ×ˢ Ioo b c))
    (hv : IntegrableOn v (U ×ˢ Ioo b c)) (j : Fin d)
    (hgrad : ∀ ψ : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U ×ˢ Ioo b c →
      (∫ z, u z * (fderiv ℝ ψ z (EinsteinRelation.unitVector j, 0) : ℂ)
        ∂((volume.restrict (Prod.fst '' tsupport ψ)).prod
          (volume.restrict (Icc b c)))) =
        -(∫ z, v z * (ψ z : ℂ)
          ∂((volume.restrict (Prod.fst '' tsupport ψ)).prod
            (volume.restrict (Icc b c)))))
    {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U ×ˢ Ioo b c) :
    (∫ z in U ×ˢ Ioo b c,
      u z * (fderiv ℝ φ z (EinsteinRelation.unitVector j, 0) : ℂ)) =
      -(∫ z in U ×ˢ Ioo b c, v z * (φ z : ℂ)) := by
  have : (volume : Measure (Vec d × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  apply eq_neg_of_add_eq_zero_left
  have he := holderComparison_complex_weak_identity_C1_of_smooth volume
    (hU.prod isOpen_Ioo) (fun _ : Unit => (EinsteinRelation.unitVector j, (0 : ℝ)))
    (fun _ : Unit => u) v (fun _ => hu) hv
    (fun ψ hψ hcψ hsψ => ?_) φ hφ hc hs
  · simpa only [Fintype.sum_unique] using he
  · have hleft := holderComparison_joint_test_pairing_localize hsψ
      (F := fun z => u z * (fderiv ℝ ψ z (EinsteinRelation.unitVector j, 0) : ℂ))
      (by
        intro z hz
        have hd : fderiv ℝ ψ z = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hz (tsupport_fderiv_subset ℝ h))
        simp only [hd, zero_apply, Complex.ofReal_zero, mul_zero])
    have hright := holderComparison_joint_test_pairing_localize hsψ
      (F := fun z => v z * (ψ z : ℂ)) (by
        intro z hz
        rw [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, mul_zero])
    have hg := hgrad ψ hψ hcψ hsψ
    rw [hleft, hright] at hg
    simpa only [Fintype.sum_unique] using add_eq_zero_iff_eq_neg.mpr hg

/-- A complex forced heat identity on an open cylinder extends to compact
C1 tests with the same flux and source. -/
theorem holderComparison_joint_weak_heat_C1
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {b c : ℝ}
    {u S : Vec d × ℝ → ℂ} {G : Fin d → Vec d × ℝ → ℂ}
    (hu : IntegrableOn u (U ×ˢ Ioo b c))
    (hG : ∀ j, IntegrableOn (G j) (U ×ˢ Ioo b c))
    (hS : IntegrableOn S (U ×ˢ Ioo b c))
    (hheat : ∀ ψ : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U ×ˢ Ioo b c →
      (∫ z in U ×ˢ Ioo b c, u z * (fderiv ℝ ψ z (0, 1) : ℂ)) =
        (∑ j, ∫ z in U ×ˢ Ioo b c,
          G j z * (fderiv ℝ ψ z (EinsteinRelation.unitVector j, 0) : ℂ)) +
        ∫ z in U ×ˢ Ioo b c, S z * (ψ z : ℂ))
    {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U ×ˢ Ioo b c) :
    (∫ z in U ×ˢ Ioo b c, u z * (fderiv ℝ φ z (0, 1) : ℂ)) =
      (∑ j, ∫ z in U ×ˢ Ioo b c,
        G j z * (fderiv ℝ φ z (EinsteinRelation.unitVector j, 0) : ℂ)) +
      ∫ z in U ×ˢ Ioo b c, S z * (φ z : ℂ) := by
  have : (volume : Measure (Vec d × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let w : Option (Fin d) → Vec d × ℝ :=
    fun j => j.elim (0, 1) (fun k => (EinsteinRelation.unitVector k, 0))
  let A : Option (Fin d) → Vec d × ℝ → ℂ :=
    fun j => j.elim u (fun k z => -G k z)
  have hA : ∀ j, IntegrableOn (A j) (U ×ˢ Ioo b c) := by
    intro j
    cases j with
    | none => exact hu
    | some k => exact (hG k).neg
  have he := holderComparison_complex_weak_identity_C1_of_smooth volume
    (hU.prod isOpen_Ioo) w A (fun z => -S z) hA hS.neg
    (fun ψ hψ hcψ hsψ => ?_) φ hφ hc hs
  · simp only [Fintype.sum_option, A, w, Option.elim_none, Option.elim_some,
      neg_mul, integral_neg, Finset.sum_neg_distrib] at he
    linear_combination he
  · simp only [Fintype.sum_option, A, w, Option.elim_none, Option.elim_some,
      neg_mul, integral_neg, Finset.sum_neg_distrib]
    rw [hheat ψ hψ hcψ hsψ]
    ring

/-- A support-based slab pairing localizes to any containing open cylinder,
including when the slab endpoints are chosen independently of the cylinder. -/
theorem holderComparison_joint_test_pairing_localize_between
    {d : ℕ} {U : Set (Vec d)} {a b c e : ℝ} {φ : Vec d × ℝ → ℝ}
    (hs : tsupport φ ⊆ U ×ˢ Ioo b c) (hab : a ≤ b) (hce : c ≤ e)
    {F : Vec d × ℝ → ℂ} (hF : ∀ z, z ∉ tsupport φ → F z = 0) :
    (∫ z, F z ∂((volume.restrict (Prod.fst '' tsupport φ)).prod
      (volume.restrict (Icc a e)))) = ∫ z in U ×ˢ Ioo b c, F z := by
  have hlocal : tsupport φ ⊆ (Prod.fst '' tsupport φ) ×ˢ Icc a e := by
    intro z hz
    exact ⟨⟨z, hz, rfl⟩, hab.trans (hs hz).2.1.le, (hs hz).2.2.le.trans hce⟩
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  calc
    _ = ∫ z, F z := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => hF z (fun h => hz (hlocal h)))
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => hF z (fun h => hz (hs h)))).symm

/-- The joint derivative pairing localizes to a cylinder contained in the
chosen time slab. No integrability outside the cylinder is required. -/
theorem holderComparison_joint_derivative_pairing_localize
    {d : ℕ} {U : Set (Vec d)} {a b c e : ℝ} {φ : Vec d × ℝ → ℝ}
    (hs : tsupport φ ⊆ U ×ˢ Ioo b c) (hab : a ≤ b) (hce : c ≤ e)
    (u : Vec d × ℝ → ℂ) (w : Vec d × ℝ) :
    (∫ z, u z * (fderiv ℝ φ z w : ℂ)
      ∂((volume.restrict (Prod.fst '' tsupport φ)).prod (volume.restrict (Icc a e)))) =
      ∫ z in U ×ˢ Ioo b c, u z * (fderiv ℝ φ z w : ℂ) := by
  apply holderComparison_joint_test_pairing_localize_between hs hab hce
  intro z hz
  have hd : fderiv ℝ φ z = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hz (tsupport_fderiv_subset ℝ h))
  simp only [hd, zero_apply, Complex.ofReal_zero, mul_zero]

/-- The joint value pairing localizes to a cylinder contained in the chosen
slab, with no integrability premise away from the test support. -/
theorem holderComparison_joint_value_pairing_localize
    {d : ℕ} {U : Set (Vec d)} {a b c e : ℝ} {φ : Vec d × ℝ → ℝ}
    (hs : tsupport φ ⊆ U ×ˢ Ioo b c) (hab : a ≤ b) (hce : c ≤ e)
    (u : Vec d × ℝ → ℂ) :
    (∫ z, u z * (φ z : ℂ)
      ∂((volume.restrict (Prod.fst '' tsupport φ)).prod (volume.restrict (Icc a e)))) =
      ∫ z in U ×ˢ Ioo b c, u z * (φ z : ℂ) := by
  apply holderComparison_joint_test_pairing_localize_between hs hab hce
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, mul_zero]

/-- Restricting a spatial-first local product Lp bound to an open cylinder
preserves the original field and its exponent. -/
theorem holderComparison_memLp_restrict_cylinder
    {d : ℕ} {U K : Set (Vec d)} {b c : ℝ} {p : ℝ≥0∞}
    (hUK : U ⊆ K) {u : Vec d × ℝ → ℂ}
    (hu : MemLp u p ((volume.restrict K).prod (volume.restrict (Icc b c)))) :
    MemLp u p (volume.restrict (U ×ˢ Ioo b c)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hu
  exact hu.mono_measure (Measure.restrict_mono
    (Set.prod_mono hUK Ioo_subset_Icc_self) le_rfl)

end EinsteinFull
