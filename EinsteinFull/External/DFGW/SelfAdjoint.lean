import EinsteinFull.External.DFGW.DetailedBalance
import EinsteinFull.External.DFGW.TransitionOperator
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Self-adjoint transition operators

Detailed balance extends kernel symmetry to square-integrable observables and gives a
self-adjoint transition operator on `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The transition-kernel pairing is symmetric for `L²` observables. -/
theorem integral_kernel_mul_comm_L2 (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) (f g : Lp ℝ 2 μ) :
    (∫ x, f x * ∫ y, g y ∂T t x ∂μ) =
      ∫ x, g x * ∫ y, f y ∂T t x ∂μ := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  let ν := μ ⊗ₘ T t
  have hfst : MeasurePreserving Prod.fst ν μ :=
    ⟨measurable_fst, Measure.fst_compProd μ (T t)⟩
  have hsnd : MeasurePreserving Prod.snd ν μ := by
    refine ⟨measurable_snd, ?_⟩
    change (μ ⊗ₘ T t).snd = μ
    rw [Measure.snd_compProd, kernel_comp_eq hP t]
  have hfg : Integrable (fun z : S × S => f z.1 * g z.2) ν := by
    have h := ((Lp.memLp f).comp_measurePreserving hfst).integrable_mul
      ((Lp.memLp g).comp_measurePreserving hsnd)
    exact h.congr (ae_of_all _ fun z => by rfl)
  have hgf : Integrable (fun z : S × S => g z.1 * f z.2) ν := by
    have h := ((Lp.memLp g).comp_measurePreserving hfst).integrable_mul
      ((Lp.memLp f).comp_measurePreserving hsnd)
    exact h.congr (ae_of_all _ fun z => by rfl)
  have hmap := integral_map (μ := ν) measurable_swap.aemeasurable
    (f := fun z : S × S => f z.1 * g z.2) (by
      change AEStronglyMeasurable _ ((μ ⊗ₘ T t).map Prod.swap)
      rw [compProd_map_swap_eq hP t]
      exact hfg.aestronglyMeasurable)
  change (∫ z, f z.1 * g z.2 ∂(ν.map Prod.swap)) =
    ∫ z, f z.2 * g z.1 ∂ν at hmap
  have hs : (∫ z : S × S, f z.1 * g z.2 ∂ν) =
      ∫ z : S × S, g z.1 * f z.2 ∂ν := by
    rw [show ν.map Prod.swap = ν from compProd_map_swap_eq hP t] at hmap
    simpa only [mul_comm] using hmap
  rw [Measure.integral_compProd hfg, Measure.integral_compProd hgf] at hs
  simpa only [integral_const_mul] using hs

/-- The `L²` transition operator is symmetric with respect to the real inner product. -/
theorem inner_transitionOperator (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) (f g : Lp ℝ 2 μ) :
    inner ℝ (transitionOperator hP t f) g = inner ℝ f (transitionOperator hP t g) := by
  calc
    inner ℝ (transitionOperator hP t f) g =
        ∫ x, g x * ∫ y, f y ∂T t x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [transitionOperator_ae_eq hP t f] with x hx
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx]
    _ = ∫ x, f x * ∫ y, g y ∂T t x ∂μ := integral_kernel_mul_comm_L2 hP t g f
    _ = inner ℝ f (transitionOperator hP t g) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [transitionOperator_ae_eq hP t g] with x hx
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, mul_comm]

/-- Each transition operator is self-adjoint on `L²` of the stationary marginal. -/
theorem isSelfAdjoint_transitionOperator (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) : IsSelfAdjoint (transitionOperator hP t) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (inner_transitionOperator hP t)

end EinsteinFull.External.DFGW
