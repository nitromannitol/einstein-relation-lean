import EllipticRegularity.Parabolic.ParabolicDef
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Affine images of library weak solutions

`M - u`, `u - m` and, more generally, `μ + λ u` of an energy-class function (on a domain of finite
measure) are again energy-class functions, and weak solutions are carried to weak solutions
(constants solve the equation because the test functions have compact support).
-/

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set PDE

/-- The integral of a directional derivative of a compactly supported `C¹` function vanishes. -/
theorem integral_fderiv_eq_zero_of_compactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (v : E) : ∫ x, fderiv ℝ φ x v ∂μ = 0 := by
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x => fderiv ℝ φ x v) := hc.fderiv_apply ℝ v
  have hint1 : Integrable (fun x => fderiv ℝ φ x v) μ := hdφ.integrable_of_hasCompactSupport hdc
  have hint0 : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
    (f := fun _ : E => (1 : ℝ)) (g := φ) (v := v)
    (by
      have e : (fun x => fderiv ℝ (fun _ : E => (1 : ℝ)) x v * φ x) = fun _ => (0 : ℝ) := by
        funext x
        simp [fderiv_const_apply]
      rw [e]
      exact integrable_zero _ _ _)
    (by simpa using hint1) (by simpa using hint0)
    (fun x _ => differentiableAt_const _)
    (fun x _ => (hφ.differentiable (by simp)).differentiableAt)
  simpa using h

variable {d : ℕ}

/-- Product of an `L²(K)` function with an `L²(U)` function supported in `K ⊆ U` is integrable
on `U`. -/
theorem integrableOn_mul_of_supported {U K : Set (Vec d)} {f ψ : Vec d → ℝ} (hKU : K ⊆ U)
    (hf : MemLp f 2 (volume.restrict K)) (hψ : MemLp ψ 2 (volume.restrict U))
    (hz : ∀ x, x ∉ K → ψ x = 0) : IntegrableOn (fun x => f x * ψ x) U volume := by
  have hψK : MemLp ψ 2 (volume.restrict K) := hψ.mono_measure (Measure.restrict_mono hKU le_rfl)
  have h1 : IntegrableOn (fun x => f x * ψ x) K volume := hf.integrable_mul hψK
  have hs : Function.support (fun x => f x * ψ x) ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (by simp [hz x hxK])
  have h2 : Integrable (fun x => f x * ψ x) volume :=
    (integrableOn_iff_integrable_of_support_subset hs).mp h1
  exact h2.integrableOn

/-- Affine images of weak gradients. -/
theorem hasWeakGradientOn_affine {U : Set (Vec d)} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (μ lam : ℝ) (hf : HasWeakGradientOn U f g)
    (hloc : ∀ K : Set (Vec d), IsCompact K → K ⊆ U → IntegrableOn f K volume) :
    HasWeakGradientOn U (fun x => μ + lam * f x) (fun x => lam • g x) := by
  intro i φ hφ hc hsub
  set dφ : Vec d → ℝ := fun x => fderiv ℝ φ x (basisVec i) with hdφ
  have hdφc : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφcs : HasCompactSupport dφ := hc.fderiv_apply ℝ (basisVec i)
  have hzero : ∀ x, x ∉ U → dφ x = 0 := fun x hx => by
    have hxs : x ∉ tsupport φ := fun h => hx (hsub h)
    simp [hdφ, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs]
  have hs : Function.support (fun x => f x * dφ x) ⊆ tsupport φ := by
    intro x hx
    by_contra hxs
    apply hx
    have : dφ x = 0 := by simp [hdφ, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs]
    simp [this]
  have h1 : IntegrableOn (fun x => f x * dφ x) (tsupport φ) volume :=
    (hloc _ hc.isCompact hsub).mul_continuousOn hdφc.continuousOn hc.isCompact
  have h2 : Integrable (fun x => f x * dφ x) volume :=
    (integrableOn_iff_integrable_of_support_subset hs).mp h1
  have hIU : IntegrableOn (fun x => f x * dφ x) U volume := h2.integrableOn
  have hdφU : IntegrableOn dφ U volume :=
    (hdφc.integrable_of_hasCompactSupport hdφcs).integrableOn
  have hz : ∫ x in U, dφ x ∂volume = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    exact integral_fderiv_eq_zero_of_compactSupport (hφ.of_le (by exact_mod_cast le_top)) hc _
  have hmain := hf i φ hφ hc hsub
  have e1 : ∫ x in U, (μ + lam * f x) * dφ x ∂volume =
      μ * ∫ x in U, dφ x ∂volume + lam * ∫ x in U, f x * dφ x ∂volume := by
    have : (fun x => (μ + lam * f x) * dφ x) = fun x => μ * dφ x + lam * (f x * dφ x) := by
      funext x; ring
    rw [this, integral_add (hdφU.const_mul μ) (hIU.const_mul lam), integral_const_mul,
      integral_const_mul]
  show ∫ x in U, (μ + lam * f x) * dφ x ∂volume =
    -∫ x in U, (lam • g x) i * φ x ∂volume
  rw [e1, hz, mul_zero, zero_add]
  have e2 : ∫ x in U, (lam • g x) i * φ x ∂volume = lam * ∫ x in U, g x i * φ x ∂volume := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e2, hmain]
  ring

end EinsteinFull.ParabolicBridge
