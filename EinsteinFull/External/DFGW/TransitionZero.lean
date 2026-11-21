import EinsteinFull.External.DFGW.JointLaw
import EinsteinFull.External.DFGW.SelfAdjoint

/-! # The transition operator at time zero

The two-time law at zero is the diagonal coupling of the stationary marginal. Its `L²`
transition operator is therefore the identity.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The zero-time joint law is the diagonal image of the stationary marginal. -/
theorem compProd_zero_eq_map_diag (hP : Draft.IsDFGWTrajectoryProcess P μ T) :
    μ ⊗ₘ T 0 = μ.map (fun x => (x, x)) := by
  have hm : Measurable (fun x : S => (x, x)) := measurable_id.prodMk measurable_id
  rw [← map_pair_eq_compProd hP 0, ← hP.marginal 0,
    Measure.map_map hm (continuous_eval_const 0).measurable]
  rfl

/-- The transition operator at time zero is the identity on `L²`. -/
theorem transitionOperator_zero (hP : Draft.IsDFGWTrajectoryProcess P μ T) :
    transitionOperator hP 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let : IsMarkovKernel (T 0) := hP.markov_kernel 0
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  let ν := μ ⊗ₘ T 0
  have hfst : MeasurePreserving Prod.fst ν μ :=
    ⟨measurable_fst, Measure.fst_compProd μ (T 0)⟩
  have hsnd : MeasurePreserving Prod.snd ν μ := by
    refine ⟨measurable_snd, ?_⟩
    change (μ ⊗ₘ T 0).snd = μ
    rw [Measure.snd_compProd, kernel_comp_eq hP 0]
  have hgf : Integrable (fun z : S × S => g z.1 * f z.2) ν := by
    have h := ((Lp.memLp g).comp_measurePreserving hfst).integrable_mul
      ((Lp.memLp f).comp_measurePreserving hsnd)
    exact h.congr (ae_of_all _ fun z => by rfl)
  have hm : Measurable (fun x : S => (x, x)) := measurable_id.prodMk measurable_id
  have hdiag := integral_map (μ := μ) hm.aemeasurable
    (f := fun z : S × S => g z.1 * f z.2) (by
      rw [← compProd_zero_eq_map_diag hP]
      exact hgf.aestronglyMeasurable)
  rw [← compProd_zero_eq_map_diag hP] at hdiag
  have hjoint : (∫ z : S × S, g z.1 * f z.2 ∂ν) = ∫ x, g x * f x ∂μ := hdiag
  rw [Measure.integral_compProd hgf] at hjoint
  simp only [integral_const_mul] at hjoint
  calc
    inner ℝ g (transitionOperator hP 0 f) = ∫ x, g x * ∫ y, f y ∂T 0 x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [transitionOperator_ae_eq hP 0 f] with x hx
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, mul_comm]
    _ = ∫ x, g x * f x ∂μ := hjoint
    _ = inner ℝ g ((ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)) f) := by
      rw [ContinuousLinearMap.id_apply, L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]

end EinsteinFull.External.DFGW
