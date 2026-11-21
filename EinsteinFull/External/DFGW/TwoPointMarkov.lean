import EinsteinFull.External.DFGW.KernelSemigroup
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Conditional expectation of a two-point observable

The Markov property computes the conditional expectation of a product of two future
state observables by successive applications of the transition kernels.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The conditional expectation of a product of two future observables factors through
successive transition kernels. -/
theorem condExp_two_state_observables (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (s t : ℝ≥0) (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C, ∀ x, |f x| ≤ C) (hgb : ∃ C, ∀ x, |g x| ≤ C) :
    P[fun η : C(ℝ, S) => f (η s) * g (η ((t : ℝ) + s)) |
      Draft.dfgwCoordSigma (Set.Iic 0)] =ᵐ[P]
      fun η => ∫ x, f x * (∫ y, g y ∂T t x) ∂T s (η 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨D, hD⟩ := hgb
  let G : S → ℝ := fun x => ∫ y, g y ∂T t x
  have hG : Measurable G := (hg.stronglyMeasurable.integral_kernel (κ := T t)).measurable
  have hGb (x : S) : |G x| ≤ D := by
    have h := norm_integral_le_of_norm_le_const (μ := T t x) (f := g) (C := D)
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hD y)
    simpa only [G, Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
      mul_one] using h
  let F : S → ℝ := fun x => f x * G x
  have hF : Measurable F := hf.mul hG
  have hFb : ∃ C, ∀ x, |F x| ≤ C := by
    refine ⟨C * D, fun x => ?_⟩
    change |f x * G x| ≤ C * D
    rw [abs_mul]
    exact mul_le_mul (hC x) (hGb x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwCoordSigma (Set.Iic (s : ℝ)) := by
    apply iSup₂_le
    intro u hu
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic (s : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) u
      (by change u ≤ (s : ℝ); have : u ≤ 0 := hu; linarith [s.coe_nonneg]) le_rfl
  have hσs : Draft.dfgwCoordSigma (S := S) (Set.Iic (s : ℝ)) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le s
  have heval : Measurable[Draft.dfgwCoordSigma (S := S) (Set.Iic (s : ℝ))]
      (fun η : C(ℝ, S) => η s) := by
    apply Measurable.of_comap_le
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic (s : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance)
      (s : ℝ) (by change (s : ℝ) ≤ s; exact le_rfl) le_rfl
  let A : C(ℝ, S) → ℝ := fun η => f (η s)
  let B : C(ℝ, S) → ℝ := fun η => g (η ((t : ℝ) + s))
  have hA : StronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] A :=
    (hf.comp heval).stronglyMeasurable
  have hB : Integrable B P := Integrable.of_bound
    (hg.comp (continuous_eval_const _).measurable).aestronglyMeasurable D
    (ae_of_all P fun η => by simpa only [B, Real.norm_eq_abs] using hD (η ((t : ℝ) + s)))
  have hAB : Integrable (A * B) P := by
    have h := hB.mul_bdd (hf.comp (continuous_eval_const (s : ℝ)).measurable).aestronglyMeasurable
      (ae_of_all P fun η => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hC (η s))
    exact h.congr (ae_of_all _ fun η => by simp only [Pi.mul_apply, A, B, Function.comp_apply, mul_comm])
  have hpull := condExp_mul_of_stronglyMeasurable_left hA hAB hB
  have hmark := condExp_shifted hP (s : ℝ) t g hg ⟨D, hD⟩
  have hstep : P[A * B | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] =ᵐ[P]
      fun η : C(ℝ, S) => F (η s) := by
    filter_upwards [hpull, hmark] with η hp hm
    simpa only [Pi.mul_apply, A, B, F, G] using hp.trans (congrArg (fun z => f (η s) * z) hm)
  have htower := condExp_condExp_of_le (μ := P) (f := A * B) hσ hσs
  have hcongr := condExp_congr_ae (m := Draft.dfgwCoordSigma (Set.Iic 0)) hstep
  have hlast := hP.markov s F hF hFb
  exact htower.symm.trans (hcongr.trans hlast)

end EinsteinFull.External.DFGW
