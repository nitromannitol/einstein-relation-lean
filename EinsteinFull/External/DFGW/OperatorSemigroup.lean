import EinsteinFull.External.DFGW.TransitionZero
import EinsteinFull.External.DFGW.KernelSemigroup
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # Semigroup law on `L²`

The Chapman–Kolmogorov identity on bounded observables extends by density and continuity
to the stationary `L²` transition operators.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The `L²` transition operators satisfy the semigroup composition law. -/
theorem transitionOperator_add (hP : Draft.IsDFGWTrajectoryProcess P μ T) (s t : ℝ≥0) :
    transitionOperator hP (s + t) = (transitionOperator hP s).comp (transitionOperator hP t) := by
  have hs : T s ∘ₘ μ ≤ μ := le_of_eq (kernel_comp_eq hP s)
  have ht : T t ∘ₘ μ ≤ μ := le_of_eq (kernel_comp_eq hP t)
  have hst : T (s + t) ∘ₘ μ ≤ μ := le_of_eq (kernel_comp_eq hP (s + t))
  have hsimple : ∀ f : Lp.simpleFunc ℝ 2 μ,
      transitionOperator hP (s + t) f = transitionOperator hP s (transitionOperator hP t f) := by
    intro f
    let u := Lp.simpleFunc.toSimpleFunc f
    have hu : Measurable u := u.measurable
    have hub : ∃ C, ∀ x, |u x| ≤ C := by
      obtain ⟨C, hC⟩ := u.exists_forall_norm_le
      exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩
    have huf : (u : S → ℝ) =ᵐ[μ] (f : Lp ℝ 2 μ) := Lp.simpleFunc.toSimpleFunc_eq_toFun f
    have htu := MarkovProcess.kernelIntegral_congr_ae ht huf
    have hstu := MarkovProcess.kernelIntegral_congr_ae hst huf
    have houter := MarkovProcess.kernelIntegral_congr_ae hs (transitionOperator_ae_eq hP t f)
    have houter' := MarkovProcess.kernelIntegral_congr_ae hs htu
    have hCK := kernel_integral_add_ae hP s t u hu hub
    apply Lp.ext
    filter_upwards [transitionOperator_ae_eq hP (s + t) f,
      transitionOperator_ae_eq hP s (transitionOperator hP t f),
      hstu, houter, houter', hCK] with x h₁ h₂ h₃ h₄ h₅ h₆
    change (transitionOperator hP (s + t) f) x =
      (transitionOperator hP s (transitionOperator hP t f)) x
    rw [h₁, h₂]
    change MarkovProcess.kernelIntegral (T (s + t)) (f : Lp ℝ 2 μ) x =
      MarkovProcess.kernelIntegral (T s) (transitionOperator hP t f) x
    exact h₃.symm.trans (h₆.symm.trans (h₅.trans h₄.symm))
  have hfun : (fun f : Lp ℝ 2 μ => transitionOperator hP (s + t) f) =
      fun f => transitionOperator hP s (transitionOperator hP t f) := by
    apply (Lp.simpleFunc.denseRange (E := ℝ) (μ := μ) (p := 2) (by simp)).equalizer
      (transitionOperator hP (s + t)).continuous
      ((transitionOperator hP s).continuous.comp (transitionOperator hP t).continuous)
    funext f
    exact hsimple f
  apply ContinuousLinearMap.ext
  intro f
  exact congrFun hfun f

end EinsteinFull.External.DFGW
