import EinsteinFull.Calculus.PhysicalDomainSupport
import EinsteinRelation.Correctors.Sol04WholeSpaceH1Testing
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Whole-space integration by parts on the actual complex physical H1 domain.

Reuses the proved real L2 divergence testing theorem from EinsteinRelation,
`Correctors/Sol04WholeSpaceH1Testing.lean`, revision
`7748a8e9000034825873768d309be8915ae53b07`. A single-coordinate vector field
turns its divergence identity into partial integration; the real and imaginary
parts give the bilinear complex identity and the vanishing real cross term.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Whole-space integration by parts for an L2 weak partial derivative. -/
theorem integral_mul_weakPartial {d : ℕ} (j : Fin d)
    {f df v : Vec d → ℝ} {H : Vec d → Vec d}
    (hf : HasWeakPartialDerivative Set.univ j f df)
    (hv : HasWeakGradient Set.univ v H)
    (hf2 : MemLp f 2 volume) (hdf2 : MemLp df 2 volume)
    (hv2 : MemLp v 2 volume) (hH2 : ∀ k, MemLp (fun x => H x k) 2 volume) :
    (∫ x, f x * H x j) = -(∫ x, df x * v x) := by
  classical
  let F : Vec d → Vec d := fun x => Pi.single j (f x)
  have hdiv : HasWeakDivergence Set.univ F df := by
    refine ⟨?_, hf.2.1, ?_⟩
    · intro k
      by_cases hk : j = k
      · subst k
        simpa only [F, Pi.single_eq_same] using hf.1
      · simpa only [F, Pi.single_eq_of_ne (Ne.symm hk)] using
          (locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ : Vec d => (0 : ℝ)) Set.univ volume)
    · intro φ hφ
      simpa [F, dot, Pi.single_apply, gradient] using! hf.2.2 φ hφ
  have hF2 k : MemLp (fun x => F x k) 2 volume := by
    by_cases hk : j = k
    · subst k
      simpa only [F, Pi.single_eq_same] using hf2
    · simpa only [F, Pi.single_eq_of_ne (Ne.symm hk)] using!
        (MemLp.zero : MemLp (fun _ : Vec d => (0 : ℝ)) 2 volume)
  simpa [F, dot, Pi.single_apply] using
    Correctors.sol04_weakDivergence_test_H1 hdiv hv hv2 hH2 hF2 hdf2

/-- Bilinear whole-space integration by parts on the actual complex H1 graph. -/
theorem physicalH1Graph_integral_mul_gradient {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) (j : Fin d) :
    (∫ x, u x * H j x) = -(∫ x, G j x * v x) := by
  have hrr := integral_mul_weakPartial j (hu.1 j) hv.1
    (Lp.memLp u).re (Lp.memLp (G j)).re (Lp.memLp v).re (fun k => (Lp.memLp (H k)).re)
  have hii := integral_mul_weakPartial j (hu.2 j) hv.2
    (Lp.memLp u).im (Lp.memLp (G j)).im (Lp.memLp v).im (fun k => (Lp.memLp (H k)).im)
  have hri := integral_mul_weakPartial j (hu.1 j) hv.2
    (Lp.memLp u).re (Lp.memLp (G j)).re (Lp.memLp v).im (fun k => (Lp.memLp (H k)).im)
  have hir := integral_mul_weakPartial j (hu.2 j) hv.1
    (Lp.memLp u).im (Lp.memLp (G j)).im (Lp.memLp v).re (fun k => (Lp.memLp (H k)).re)
  have hUH : Integrable (fun x => u x * H j x) volume := (Lp.memLp u).integrable_mul (Lp.memLp (H j))
  have hGv : Integrable (fun x => G j x * v x) volume := (Lp.memLp (G j)).integrable_mul (Lp.memLp v)
  apply Complex.ext
  · simp only [Complex.neg_re]
    change RCLike.re (∫ x, u x * H j x) = -RCLike.re (∫ x, G j x * v x)
    rw [← integral_re hUH, ← integral_re hGv]
    simp only [RCLike.re_eq_complex_re, Complex.mul_re]
    rw [integral_sub (f := fun x => (u x).re * (H j x).re)
      (g := fun x => (u x).im * (H j x).im) ((Lp.memLp u).re.integrable_mul (Lp.memLp (H j)).re)
      ((Lp.memLp u).im.integrable_mul (Lp.memLp (H j)).im),
      integral_sub (f := fun x => (G j x).re * (v x).re)
      (g := fun x => (G j x).im * (v x).im) ((Lp.memLp (G j)).re.integrable_mul (Lp.memLp v).re)
      ((Lp.memLp (G j)).im.integrable_mul (Lp.memLp v).im), hrr, hii]
    ring
  · simp only [Complex.neg_im]
    change RCLike.im (∫ x, u x * H j x) = -RCLike.im (∫ x, G j x * v x)
    rw [← integral_im hUH, ← integral_im hGv]
    simp only [RCLike.im_eq_complex_im, Complex.mul_im]
    rw [integral_add (f := fun x => (u x).re * (H j x).im)
      (g := fun x => (u x).im * (H j x).re) ((Lp.memLp u).re.integrable_mul (Lp.memLp (H j)).im)
      ((Lp.memLp u).im.integrable_mul (Lp.memLp (H j)).re),
      integral_add (f := fun x => (G j x).re * (v x).im)
      (g := fun x => (G j x).im * (v x).re) ((Lp.memLp (G j)).re.integrable_mul (Lp.memLp v).im)
      ((Lp.memLp (G j)).im.integrable_mul (Lp.memLp v).re), hri, hir]
    ring

/-- The global real H1 derivative pairing has no boundary contribution. -/
theorem integral_mul_weakGradient_self {d : ℕ} (j : Fin d)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : HasWeakGradient Set.univ u G) (hu2 : MemLp u 2 volume)
    (hG2 : ∀ k, MemLp (fun x => G x k) 2 volume) :
    (∫ x, u x * G x j) = 0 := by
  have h := integral_mul_weakPartial j (hu j) hu hu2 (hG2 j) hu2 hG2
  have hc : (∫ x, G x j * u x) = ∫ x, u x * G x j := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [hc] at h
  linarith only [h]

/-- The real conjugate-gradient cross term vanishes on the full complex H1 domain. -/
theorem physicalH1Graph_integral_re_star_mul_gradient_zero {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) (j : Fin d) :
    (∫ x, (star (u x) * G j x).re) = 0 := by
  have hr := integral_mul_weakGradient_self j hu.1 (Lp.memLp u).re
    (fun k => (Lp.memLp (G k)).re)
  have hi := integral_mul_weakGradient_self j hu.2 (Lp.memLp u).im
    (fun k => (Lp.memLp (G k)).im)
  have hpoint (x : Vec d) : (star (u x) * G j x).re =
      (u x).re * (G j x).re + (u x).im * (G j x).im := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  simp_rw [hpoint]
  rw [integral_add (f := fun x => (u x).re * (G j x).re)
    (g := fun x => (u x).im * (G j x).im)
    ((Lp.memLp u).re.integrable_mul (Lp.memLp (G j)).re)
    ((Lp.memLp u).im.integrable_mul (Lp.memLp (G j)).im), hr, hi, zero_add]

end EinsteinFull
