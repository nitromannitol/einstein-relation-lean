import EinsteinFull.Calculus.GaussianProfileSupport
import EinsteinFull.Frozen.KernelProfileRemainder
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import EinsteinFull.Frozen.IntegratedRemainderCoefficient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace EinsteinFull

/-- The prescribed Gaussian profile is entire. -/
theorem differentiable_complexGaussianProfile (u₀ u₂ γ : ℝ) :
    Differentiable ℂ (complexGaussianProfile u₀ u₂ γ) := by
  unfold complexGaussianProfile
  fun_prop

/-- The profile subtraction preserves holomorphy at every fixed time. -/
theorem differentiable_kernelProfileRemainder (d : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ) (t : ℝ) (hK : Differentiable ℂ (K t)) :
    Differentiable ℂ (kernelProfileRemainder d u₀ u₂ γ K t) := by
  unfold kernelProfileRemainder
  split_ifs
  · exact hK.sub (differentiable_const _ |>.mul
      ((differentiable_complexGaussianProfile u₀ u₂ γ).comp
        (differentiable_id.mul_const _)))
  · exact hK.sub (differentiable_const _)

/-- Real force coefficients use genuine derivatives of a smooth real function. -/
theorem contDiff_kernelProfileRemainder_re (d : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ) (t : ℝ) (hK : Differentiable ℂ (K t)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun lam : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) := by
  exact (differentiable_kernelProfileRemainder d u₀ u₂ γ K t hK).contDiff.real_of_complex

/-- Every force derivative used in the coefficient is the actual next derivative. -/
theorem hasDerivAt_iteratedDeriv_kernelProfileRemainder_re
    (d : ℕ) (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ) (t : ℝ)
    (hK : Differentiable ℂ (K t)) (m : ℕ) :
    HasDerivAt
      (iteratedDeriv m (fun lam : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re))
      (iteratedDeriv (m + 1) (fun lam : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0) 0 := by
  have hf := contDiff_kernelProfileRemainder_re d u₀ u₂ γ K t hK
  have hm := hf.differentiable_iteratedDeriv m (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)
  simpa only [iteratedDeriv_succ] using (hm 0).hasDerivAt

/-- On the public reality domain, projection retains the entire remainder. -/
theorem kernelProfileRemainder_eq_ofReal_re (d : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ) (t : ℝ)
    (hR : ∀ lam : ℝ, (K t (lam : ℂ)).im = 0) (lam : ℝ) :
    kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ) =
      ((kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im]
    unfold kernelProfileRemainder
    split_ifs
    · rw [← Complex.ofReal_mul, complexGaussianProfile_ofReal]
      simp only [Complex.sub_im, hR lam, Complex.mul_im, Complex.ofReal_im,
        mul_zero, zero_mul, add_zero, sub_zero]
    · simp only [sub_zero, hR lam]

/-- Scalar embedding commutes with every actual derivative of a smooth function. -/
theorem iteratedDeriv_ofReal_of_contDiff (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    iteratedDeriv n (fun x => (f x : ℂ)) = fun x => (iteratedDeriv (F := ℝ) n f x : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
    funext x
    exact (((hf.differentiable_iteratedDeriv n
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) x).hasDerivAt.ofReal_comp).deriv

/-- Real-part differentiation equals differentiation of the actual remainder. -/
theorem iteratedDeriv_kernelProfileRemainder_eq_ofReal (d : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ) (t : ℝ) (hK : Differentiable ℂ (K t))
    (hR : ∀ lam : ℝ, (K t (lam : ℂ)).im = 0) (n : ℕ) (lam : ℝ) :
    iteratedDeriv n (fun r : ℝ => kernelProfileRemainder d u₀ u₂ γ K t (r : ℂ)) lam =
      (iteratedDeriv (F := ℝ) n (fun r : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (r : ℂ)).re) lam : ℂ) := by
  have he : (fun r : ℝ => kernelProfileRemainder d u₀ u₂ γ K t (r : ℂ)) =
      fun r : ℝ => ((kernelProfileRemainder d u₀ u₂ γ K t (r : ℂ)).re : ℂ) :=
    funext (kernelProfileRemainder_eq_ofReal_re d u₀ u₂ γ K t hR)
  rw [he, iteratedDeriv_ofReal_of_contDiff _
    (contDiff_kernelProfileRemainder_re d u₀ u₂ γ K t hK)]

/-- The coefficient integrates the actual complex remainder derivative, with
genuine complex integrability supplied by its public real integral witness. -/
theorem integratedRemainderCoefficient_complex_integral (d : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ) (hK : ∀ t : ℝ, 0 ≤ t → Differentiable ℂ (K t))
    (hR : ∀ t : ℝ, 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0)
    (j : Fin (d + 1))
    (hI : MeasureTheory.IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
        (j.val.factorial : ℝ)) (Set.Ici 0)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
      kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)) 0 /
        (j.val.factorial : ℂ)) (Set.Ici 0) ∧
    (∫ t in Set.Ici (0 : ℝ), iteratedDeriv j.val (fun lam : ℝ =>
      kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)) 0 / (j.val.factorial : ℂ)) =
      (integratedRemainderCoefficient d u₀ u₂ γ K hK hR j hI : ℂ) := by
  have he : (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
      kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)) 0 / (j.val.factorial : ℂ)) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ici 0)]
      fun t : ℝ => ((iteratedDeriv j.val (fun lam : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
          (j.val.factorial : ℝ) : ℝ) : ℂ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    rw [iteratedDeriv_kernelProfileRemainder_eq_ofReal d u₀ u₂ γ K t
      (hK t ht) (hR t ht) j.val 0]
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
  refine ⟨(Complex.ofRealCLM.integrable_comp hI).congr he.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae he, integral_complex_ofReal]
  rfl

end EinsteinFull
