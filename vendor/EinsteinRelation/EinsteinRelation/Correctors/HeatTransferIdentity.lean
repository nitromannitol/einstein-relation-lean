import EinsteinRelation.Correctors.HeatSmoothing
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Heat-kernel identity for smooth compactly supported kernels

Step 2 of Proposition 6.1 (`paper/main.tex`, equation `scalar-heat-transfer`) rests on the
identity `K * f = K * H_{r²} f - ∫_0^{r²} (ΔK) * H_t f dt` for a smooth compactly supported
kernel `K`. This file proves its analytic core for the Euclidean heat kernel
`p_t = euclideanHeatKernel t`:

* `coordLaplacian K = ΔK = ∑ᵢ ∂ᵢ² K` for a `C²` function `K : Vec d → ℝ`;
* the heat kernel solves the heat equation, `∂_t p_t(x) = Δ_x p_t(x)` for `t > 0`;
* integration by parts moves the Laplacian from a `C²` function onto a compactly supported
  `C²` kernel: `∫ K * Δφ = ∫ (ΔK) * φ`.

The Gaussian derivatives are computed from the explicit formula
`p_t(x) = (4πt)^{-d/2} exp(-|x|²/(4t))`.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-! ## The coordinate Laplacian and smoothness of partial derivatives -/

/-- The coordinate Laplacian `∑ᵢ ∂ᵢ² K` of a function on `Vec d`, where `∂ᵢ` is the Fréchet
derivative in the direction `unitVector i`. For a `C²` function `K` this is the Laplacian `ΔK`
of the identity `scalar-heat-transfer` in `paper/main.tex`. -/
def coordLaplacian (K : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, fderiv ℝ (fun y => fderiv ℝ K y (unitVector i)) x (unitVector i)

/-- The derivative of a `C²` function in a fixed direction is `C¹`. -/
theorem contDiff_one_fderiv_dir {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) (v : Vec d) :
    ContDiff ℝ 1 (fun y => fderiv ℝ K y v) := by
  have h : ContDiff ℝ 1 (fderiv ℝ K) := hK.fderiv_right (le_of_eq one_add_one_eq_two)
  exact h.clm_apply contDiff_const

/-- The derivative of a `C¹` function in a fixed direction is continuous. -/
theorem continuous_fderiv_dir {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) (v : Vec d) :
    Continuous (fun y => fderiv ℝ g y v) :=
  (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- A continuous compactly supported function times a continuous function is integrable. -/
theorem integrable_mul_of_compact_support {A B : Vec d → ℝ} (hA : Continuous A)
    (hAc : HasCompactSupport A) (hB : Continuous B) :
    Integrable (fun x => A x * B x) volume := by
  have hc : HasCompactSupport (A * B) := hAc.mul_right
  exact (hA.mul hB).integrable_of_hasCompactSupport hc

/-! ## Integration by parts against a compactly supported kernel -/

/-- Integration by parts in the direction `e`: for a compactly supported `C²` kernel `K` and a
`C²` function `φ`, `∫ K * ∂_e(∂_e φ) = ∫ ∂_e(∂_e K) * φ`. -/
theorem integral_mul_fderiv_fderiv_eq {K φ : Vec d → ℝ} (hK : ContDiff ℝ 2 K)
    (hKc : HasCompactSupport K) (hφ : ContDiff ℝ 2 φ) (e : Vec d) :
    ∫ x, K x * fderiv ℝ (fun y => fderiv ℝ φ y e) x e =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ K y e) x e * φ x := by
  have hg : ContDiff ℝ 1 (fun y => fderiv ℝ φ y e) := contDiff_one_fderiv_dir hφ e
  have hk : ContDiff ℝ 1 (fun y => fderiv ℝ K y e) := contDiff_one_fderiv_dir hK e
  have hKd : Differentiable ℝ K := hK.differentiable two_ne_zero
  have hφd : Differentiable ℝ φ := hφ.differentiable two_ne_zero
  have hgd : Differentiable ℝ (fun y => fderiv ℝ φ y e) := hg.differentiable one_ne_zero
  have hkd : Differentiable ℝ (fun y => fderiv ℝ K y e) := hk.differentiable one_ne_zero
  have hKe : HasCompactSupport (fun y => fderiv ℝ K y e) := hKc.fderiv_apply ℝ e
  have hKee : HasCompactSupport (fun x => fderiv ℝ (fun y => fderiv ℝ K y e) x e) :=
    hKe.fderiv_apply ℝ e
  have hKcont : Continuous K := hK.continuous
  have hφcont : Continuous φ := hφ.continuous
  have hke : Continuous (fun y => fderiv ℝ K y e) := hk.continuous
  have hkee : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ K y e) x e) :=
    continuous_fderiv_dir hk e
  have hge : Continuous (fun y => fderiv ℝ φ y e) := hg.continuous
  have hgee : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ φ y e) x e) :=
    continuous_fderiv_dir hg e
  have hI1 : Integrable (fun x => fderiv ℝ K x e * fderiv ℝ φ x e) volume :=
    integrable_mul_of_compact_support hke hKe hge
  have hI2 : Integrable (fun x => K x * fderiv ℝ (fun y => fderiv ℝ φ y e) x e) volume :=
    integrable_mul_of_compact_support hKcont hKc hgee
  have hI3 : Integrable (fun x => K x * fderiv ℝ φ x e) volume :=
    integrable_mul_of_compact_support hKcont hKc hge
  have hI4 : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ K y e) x e * φ x) volume :=
    integrable_mul_of_compact_support hkee hKee hφcont
  have hI6 : Integrable (fun x => fderiv ℝ K x e * φ x) volume :=
    integrable_mul_of_compact_support hke hKe hφcont
  have h1 : ∫ x, K x * fderiv ℝ (fun y => fderiv ℝ φ y e) x e =
      -∫ x, fderiv ℝ K x e * fderiv ℝ φ x e :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := K)
      (g := fun y => fderiv ℝ φ y e) (v := e) hI1 hI2 hI3
      (fun x _ => hKd x) (fun x _ => hgd x)
  have h2 : ∫ x, fderiv ℝ K x e * fderiv ℝ φ x e =
      -∫ x, fderiv ℝ (fun y => fderiv ℝ K y e) x e * φ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := fun y => fderiv ℝ K y e)
      (g := φ) (v := e) hI4 hI1 hI6
      (fun x _ => hkd x) (fun x _ => hφd x)
  rw [h1, h2, neg_neg]

/-- The integrability of `x ↦ K x * ∂_e(∂_e φ) x` used in the coordinate sum. -/
theorem integrable_mul_fderiv_fderiv {K φ : Vec d → ℝ} (hK : ContDiff ℝ 2 K)
    (hKc : HasCompactSupport K) (hφ : ContDiff ℝ 2 φ) (e : Vec d) :
    Integrable (fun x => K x * fderiv ℝ (fun y => fderiv ℝ φ y e) x e) volume :=
  integrable_mul_of_compact_support hK.continuous hKc
    (continuous_fderiv_dir (contDiff_one_fderiv_dir hφ e) e)

/-- The integrability of `x ↦ ∂_e(∂_e K) x * φ x` used in the coordinate sum. -/
theorem integrable_fderiv_fderiv_mul {K φ : Vec d → ℝ} (hK : ContDiff ℝ 2 K)
    (hKc : HasCompactSupport K) (hφ : ContDiff ℝ 2 φ) (e : Vec d) :
    Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ K y e) x e * φ x) volume :=
  integrable_mul_of_compact_support
    (continuous_fderiv_dir (contDiff_one_fderiv_dir hK e) e)
    ((hKc.fderiv_apply ℝ e).fderiv_apply ℝ e) hφ.continuous

/-- Integration by parts for the coordinate Laplacian: for a compactly supported `C²` kernel `K`
and a `C²` function `φ`, `∫ K * Δφ = ∫ (ΔK) * φ`. -/
theorem integral_mul_coordLaplacian_eq {K φ : Vec d → ℝ} (hK : ContDiff ℝ 2 K)
    (hKc : HasCompactSupport K) (hφ : ContDiff ℝ 2 φ) :
    ∫ x, K x * coordLaplacian φ x = ∫ x, coordLaplacian K x * φ x := by
  simp only [coordLaplacian, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => integrable_mul_fderiv_fderiv hK hKc hφ (unitVector i)),
    integral_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => integrable_fderiv_fderiv_mul hK hKc hφ (unitVector i))]
  exact Finset.sum_congr rfl fun i _ => integral_mul_fderiv_fderiv_eq hK hKc hφ (unitVector i)

/-! ## The Euclidean heat kernel: the Gaussian and its derivatives -/

/-- The heat kernel with the exponent written as `-(1/(4t)) * |x|²`. -/
private theorem euclideanHeatKernel_eq_exp (t : ℝ) (x : Vec d) :
    euclideanHeatKernel t x =
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * euclideanSq x) := by
  unfold euclideanHeatKernel
  rw [show -(euclideanSq x) / (4 * t) = -(1 / (4 * t)) * euclideanSq x by ring]

/-- The heat kernel as a function on `Vec d`. -/
private theorem euclideanHeatKernel_fun (t : ℝ) :
    euclideanHeatKernel (d := d) t =
      fun y => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * euclideanSq y) :=
  funext (euclideanHeatKernel_eq_exp t)

/-- The Fréchet derivative of `|x|²` at `x`, namely `v ↦ 2 ∑ⱼ xⱼ vⱼ`. -/
private def sqGradient (x : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ j, (x j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) +
    x j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ))

private theorem sqGradient_apply (x v : Vec d) :
    sqGradient x v = ∑ j, (x j * v j + x j * v j) := by
  unfold sqGradient
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

private theorem hasFDerivAt_euclideanSq (x : Vec d) :
    HasFDerivAt (fun y : Vec d => euclideanSq y) (sqGradient x) x := by
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun y : Vec d => y j * y j)
        (x j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) +
          x j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x :=
    fun j _ => (hasFDerivAt_apply (𝕜 := ℝ) j x).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) j x)
  exact HasFDerivAt.fun_sum hterm

/-- The heat kernel's Fréchet derivative at `x`, written with the Gaussian prefactor. -/
private theorem hasFDerivAt_euclideanHeatKernel_aux (t : ℝ) (x : Vec d) :
    HasFDerivAt
      (fun y : Vec d => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(1 / (4 * t)) * euclideanSq y))
      ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) •
        (Real.exp (-(1 / (4 * t)) * euclideanSq x) • (-(1 / (4 * t)) • sqGradient x))) x := by
  have h1 : HasFDerivAt (fun y : Vec d => -(1 / (4 * t)) * euclideanSq y)
      (-(1 / (4 * t)) • sqGradient x) x :=
    (hasFDerivAt_euclideanSq x).const_mul _
  exact (h1.exp).const_mul _

/-- The heat kernel is differentiable in space. -/
private theorem differentiable_euclideanHeatKernel (t : ℝ) :
    Differentiable ℝ (euclideanHeatKernel (d := d) t) := by
  rw [euclideanHeatKernel_fun t]
  exact fun x => (hasFDerivAt_euclideanHeatKernel_aux t x).differentiableAt

/-- The spatial gradient of the heat kernel: `∇p_t(x) · v = -p_t(x) (x · v) / (2t)`. -/
theorem fderiv_euclideanHeatKernel (t : ℝ) (x v : Vec d) :
    fderiv ℝ (euclideanHeatKernel (d := d) t) x v =
      euclideanHeatKernel t x * (-(1 / (2 * t)) * ∑ j, x j * v j) := by
  have hH := hasFDerivAt_euclideanHeatKernel_aux t x
  rw [← euclideanHeatKernel_fun t] at hH
  have hS : ∑ j, (x j * v j + x j * v j) = 2 * ∑ j, x j * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hH.fderiv, euclideanHeatKernel_eq_exp t x]
  simp only [ContinuousLinearMap.smul_apply, sqGradient_apply, smul_eq_mul, hS]
  ring

private theorem sum_mul_unitVector (x : Vec d) (i : Fin d) :
    ∑ j, x j * unitVector i j = x i := by
  simp [unitVector, Pi.single_apply]

private theorem unitVector_apply_self (i : Fin d) : unitVector i i = 1 := by
  simp [unitVector]

/-- The partial derivative of the heat kernel in a coordinate direction. -/
private theorem fderiv_euclideanHeatKernel_unitVector (t : ℝ) (x : Vec d) (i : Fin d) :
    fderiv ℝ (euclideanHeatKernel (d := d) t) x (unitVector i) =
      euclideanHeatKernel t x * (-(1 / (2 * t)) * x i) := by
  rw [fderiv_euclideanHeatKernel, sum_mul_unitVector]

/-- The coordinate partial derivative of the heat kernel, as a function of `y`. -/
private theorem fderiv_euclideanHeatKernel_fun_eq (t : ℝ) (i : Fin d) :
    (fun y : Vec d => fderiv ℝ (euclideanHeatKernel (d := d) t) y (unitVector i)) =
      fun y => euclideanHeatKernel t y * (-(1 / (2 * t)) * y i) :=
  funext fun y => fderiv_euclideanHeatKernel_unitVector t y i

/-- The Laplacian of the heat kernel, `Δ_x p_t(x) = (|x|²/(4t²) - d/(2t)) p_t(x)`. -/
theorem coordLaplacian_euclideanHeatKernel (t : ℝ) (x : Vec d) :
    coordLaplacian (euclideanHeatKernel (d := d) t) x =
      euclideanHeatKernel t x * (euclideanSq x / (4 * t ^ 2) - (d : ℝ) / (2 * t)) := by
  have hsecond : ∀ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ (euclideanHeatKernel (d := d) t) y (unitVector i)) x
          (unitVector i) =
        euclideanHeatKernel t x * (-(1 / (2 * t))) +
          euclideanHeatKernel t x * (-(1 / (2 * t))) ^ 2 * (x i * x i) := by
    intro i
    have hG : HasFDerivAt (fun y => euclideanHeatKernel (d := d) t y * (-(1 / (2 * t)) * y i))
        (euclideanHeatKernel t x • (-(1 / (2 * t)) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) +
          (-(1 / (2 * t)) * x i) • fderiv ℝ (euclideanHeatKernel (d := d) t) x) x :=
      (differentiable_euclideanHeatKernel t x).hasFDerivAt.fun_mul
        ((hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul _)
    rw [fderiv_euclideanHeatKernel_fun_eq t i, hG.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [fderiv_euclideanHeatKernel_unitVector, unitVector_apply_self]
    ring
  unfold coordLaplacian
  simp only [hsecond, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [euclideanSq, dot]
  ring

/-- The time derivative of the heat kernel at a fixed point, for `t > 0`. -/
theorem hasDerivAt_euclideanHeatKernel_time (x : Vec d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => euclideanHeatKernel s x)
      (euclideanHeatKernel t x * (euclideanSq x / (4 * t ^ 2) - (d : ℝ) / (2 * t))) t := by
  have ht' : t ≠ 0 := ht.ne'
  have hpi : 4 * Real.pi * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht'
  have hA : HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ (-(d : ℝ) / 2))
      (4 * Real.pi * 1 * (-(d : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2 - 1)) t :=
    ((hasDerivAt_id' t).const_mul (4 * Real.pi)).rpow_const (Or.inl hpi)
  have hinv : HasDerivAt (fun s : ℝ => (-(euclideanSq x) / 4) * s⁻¹)
      ((-(euclideanSq x) / 4) * -(t ^ 2)⁻¹) t :=
    (hasDerivAt_inv ht').const_mul (-(euclideanSq x) / 4)
  have hB : HasDerivAt (fun s : ℝ => Real.exp (-(euclideanSq x) / (4 * s)))
      (Real.exp (-(euclideanSq x) / (4 * t)) * (euclideanSq x / (4 * t ^ 2))) t := by
    have hfun : (fun s : ℝ => Real.exp (-(euclideanSq x) / (4 * s))) =
        fun s => Real.exp ((-(euclideanSq x) / 4) * s⁻¹) :=
      funext fun s => congrArg Real.exp (by ring)
    rw [hfun]
    refine (hinv.exp).congr_deriv ?_
    show Real.exp ((-(euclideanSq x) / 4) * t⁻¹) * ((-(euclideanSq x) / 4) * -(t ^ 2)⁻¹) =
      Real.exp (-(euclideanSq x) / (4 * t)) * (euclideanSq x / (4 * t ^ 2))
    rw [show (-(euclideanSq x) / 4) * t⁻¹ = -(euclideanSq x) / (4 * t) by ring]
    ring
  have hfun : (fun s : ℝ => euclideanHeatKernel s x) =
      fun s => (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-(euclideanSq x) / (4 * s)) :=
    funext fun s => rfl
  rw [hfun]
  refine (hA.fun_mul hB).congr_deriv ?_
  unfold euclideanHeatKernel
  rw [Real.rpow_sub_one hpi]
  field_simp
  ring

/-- The heat equation for the Euclidean heat kernel: `∂_t p_t(x) = Δ_x p_t(x)` for `t > 0`. -/
theorem hasDerivAt_euclideanHeatKernel_heat (x : Vec d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => euclideanHeatKernel s x)
      (coordLaplacian (euclideanHeatKernel (d := d) t) x) t := by
  rw [coordLaplacian_euclideanHeatKernel t x]
  exact hasDerivAt_euclideanHeatKernel_time x ht

end EinsteinRelation.Correctors

end
