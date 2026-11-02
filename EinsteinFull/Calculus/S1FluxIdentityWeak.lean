import EinsteinFull.Calculus.S1FluxIdentitySupport
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Weak-solution tools for `e:flux-identity`

Local integrability against smooth compact tests, symmetry of second derivatives,
the antisymmetric cancellation, and the passage from real to complex tests.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ}

theorem fluxId_intT {f : Vec d → ℂ} (hf : LocallyIntegrable f volume) {θ : Vec d → ℂ}
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) : Integrable (fun x => f x * θ x) := by
  have h := hf.integrable_smul_left_of_hasCompactSupport hθ hθc
  simp only [smul_eq_mul] at h
  exact h.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem fluxId_locInt_of_memLp {f : Vec d → ℂ}
    (hf : ∀ K : Set (Vec d), IsCompact K → MemLp f 2 (volume.restrict K)) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (hf K hK).integrable (by norm_num)

theorem fluxId_fderiv_comm {f : Vec d → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x v w : Vec d) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((contDiff_infty_iff_fderiv.mp hf).2).differentiable (by simp) x
  have key : ∀ v w : Vec d,
      fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    intro v w
    have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    rw [h.fderiv]
    simp
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  rw [key v w, key w v]
  exact hs w v

/-- The antisymmetric second-derivative sum vanishes. -/
theorem fluxId_sum_zero (Ψ : Fin d → Fin d → Vec d → ℂ)
    (hΨ : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (Ψ k j))
    (hanti : ∀ k j y, Ψ k j y = -Ψ j k y) (x : Vec d) :
    ∑ j, ∑ k, fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j) = 0 := by
  obtain ⟨U, hU⟩ : ∃ U : Fin d → Fin d → ℂ, ∀ j k, U j k =
      fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j) :=
    ⟨fun j k => fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j),
      fun _ _ => rfl⟩
  have h1 : ∀ j k, U k j = -U j k := by
    intro j k
    rw [hU, hU]
    have e1 : Ψ j k = fun y => -Ψ k j y := funext fun y => hanti j k y
    have a1 : (fun y => fderiv ℝ (fun z => -Ψ k j z) y (unitVector j)) =
        fun y => -fderiv ℝ (Ψ k j) y (unitVector j) := by
      funext y
      simp
    rw [e1, a1, fderiv_fun_neg, ContinuousLinearMap.neg_apply,
      fluxId_fderiv_comm (hΨ k j) x (unitVector j) (unitVector k)]
  have h2 : ∑ j, ∑ k, U j k = ∑ j, ∑ k, -U j k := by
    refine Eq.trans Finset.sum_comm ?_
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b
  simp only [Finset.sum_neg_distrib] at h2
  simp only [← hU]
  linear_combination (1 / 2 : ℂ) * h2

theorem fluxId_fderiv_re {θ : Vec d → ℂ} {x : Vec d} (hθ : DifferentiableAt ℝ θ x)
    (v : Vec d) : fderiv ℝ (fun y => (θ y).re) x v = (fderiv ℝ θ x v).re := by
  have h : HasFDerivAt (fun y => (θ y).re) (Complex.reCLM.comp (fderiv ℝ θ x)) x :=
    Complex.reCLM.hasFDerivAt.comp x hθ.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem fluxId_fderiv_im {θ : Vec d → ℂ} {x : Vec d} (hθ : DifferentiableAt ℝ θ x)
    (v : Vec d) : fderiv ℝ (fun y => (θ y).im) x v = (fderiv ℝ θ x v).im := by
  have h : HasFDerivAt (fun y => (θ y).im) (Complex.imCLM.comp (fderiv ℝ θ x)) x :=
    Complex.imCLM.hasFDerivAt.comp x hθ.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- A weak identity for real smooth compact tests extends to complex tests. -/
theorem fluxId_complexify (h : Vec d → ℂ) (F : Fin d → Vec d → ℂ)
    (hh : LocallyIntegrable h volume) (hF : ∀ m, LocallyIntegrable (F m) volume)
    (hw : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, h x * (φ x : ℂ) = -∑ m, ∫ x, F m x * (fderiv ℝ φ x (unitVector m) : ℂ))
    (θ : Vec d → ℂ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) :
    ∫ x, h x * θ x = -∑ m, ∫ x, F m x * fderiv ℝ θ x (unitVector m) := by
  have hθd : ∀ x, DifferentiableAt ℝ θ x := fun x => hθ.differentiable (by simp) x
  obtain ⟨θr, hθr⟩ : ∃ f : Vec d → ℝ, ∀ x, f x = (θ x).re := ⟨_, fun _ => rfl⟩
  obtain ⟨θi, hθi⟩ : ∃ f : Vec d → ℝ, ∀ x, f x = (θ x).im := ⟨_, fun _ => rfl⟩
  have hθrs : ContDiff ℝ (⊤ : ℕ∞) θr := by
    have : θr = fun x => (θ x).re := funext hθr
    rw [this]
    exact Complex.reCLM.contDiff.comp hθ
  have hθis : ContDiff ℝ (⊤ : ℕ∞) θi := by
    have : θi = fun x => (θ x).im := funext hθi
    rw [this]
    exact Complex.imCLM.contDiff.comp hθ
  have hθrc : HasCompactSupport θr := by
    have : θr = fun x => (θ x).re := funext hθr
    rw [this]
    exact hθc.comp_left (g := Complex.re) (by simp)
  have hθic : HasCompactSupport θi := by
    have : θi = fun x => (θ x).im := funext hθi
    rw [this]
    exact hθc.comp_left (g := Complex.im) (by simp)
  have hdr : ∀ x v, fderiv ℝ θr x v = (fderiv ℝ θ x v).re := by
    intro x v
    have : θr = fun x => (θ x).re := funext hθr
    rw [this]
    exact fluxId_fderiv_re (hθd x) v
  have hdi : ∀ x v, fderiv ℝ θi x v = (fderiv ℝ θ x v).im := by
    intro x v
    have : θi = fun x => (θ x).im := funext hθi
    rw [this]
    exact fluxId_fderiv_im (hθd x) v
  have hθx : ∀ x, θ x = (θr x : ℂ) + Complex.I * (θi x : ℂ) := by
    intro x
    rw [hθr, hθi, mul_comm]
    exact (Complex.re_add_im _).symm
  have hdx : ∀ x v, fderiv ℝ θ x v =
      (fderiv ℝ θr x v : ℂ) + Complex.I * (fderiv ℝ θi x v : ℂ) := by
    intro x v
    rw [hdr, hdi, mul_comm]
    exact (Complex.re_add_im _).symm
  have hcast : ∀ {f : Vec d → ℝ}, Continuous f → Continuous (fun x => (f x : ℂ)) :=
    fun hf => Complex.continuous_ofReal.comp hf
  have hcastc : ∀ {f : Vec d → ℝ}, HasCompactSupport f → HasCompactSupport (fun x => (f x : ℂ)) :=
    fun hf => hf.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
  have dc : ∀ (f : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ m : Fin d,
      Continuous (fun x => (fderiv ℝ f x (unitVector m) : ℂ)) := fun f hf m =>
    hcast ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  have dcc : ∀ (f : Vec d → ℝ), HasCompactSupport f → ∀ m : Fin d,
      HasCompactSupport (fun x => (fderiv ℝ f x (unitVector m) : ℂ)) := fun f hf m =>
    hcastc (hf.fderiv_apply ℝ (unitVector m))
  have hr := hw θr hθrs hθrc
  have hi := hw θi hθis hθic
  have iL1 := fluxId_intT hh (hcast hθrs.continuous) (hcastc hθrc)
  have iL2 := fluxId_intT hh (hcast hθis.continuous) (hcastc hθic)
  have iR1 : ∀ m, Integrable (fun x => F m x * (fderiv ℝ θr x (unitVector m) : ℂ)) := fun m =>
    fluxId_intT (hF m) (dc θr hθrs m) (dcc θr hθrc m)
  have iR2 : ∀ m, Integrable (fun x => F m x * (fderiv ℝ θi x (unitVector m) : ℂ)) := fun m =>
    fluxId_intT (hF m) (dc θi hθis m) (dcc θi hθic m)
  have hL : ∫ x, h x * θ x =
      (∫ x, h x * (θr x : ℂ)) + Complex.I * ∫ x, h x * (θi x : ℂ) := by
    rw [← integral_const_mul, ← integral_add iL1 (iL2.const_mul Complex.I)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [hθx x]
    ring
  have hR : ∀ m, ∫ x, F m x * fderiv ℝ θ x (unitVector m) =
      (∫ x, F m x * (fderiv ℝ θr x (unitVector m) : ℂ)) +
        Complex.I * ∫ x, F m x * (fderiv ℝ θi x (unitVector m) : ℂ) := by
    intro m
    rw [← integral_const_mul, ← integral_add (iR1 m) ((iR2 m).const_mul Complex.I)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [hdx x]
    ring
  rw [hL, hr, hi, Finset.sum_congr rfl (fun m _ => hR m), Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

end EinsteinFull
