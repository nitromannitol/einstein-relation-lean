import EinsteinFull.Regeneration.CappedSlabStoppedFiltration
import EinsteinFull.Calculus.U1SignedStoppingRestartSupport
import MarkovProcess.Restart.ConditionalExpectation

/-!
# Restarting capped slab increments

For a regular realization, the conditional mean of the next capped slab
increment is the initial increment mean at the current stopped position.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The next slab increment is the first increment of the path shifted to the previous exit. -/
theorem cappedSlabIncrement_succ_eq_shift {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (g : ℝ≥0) (n : ℕ) :
    cappedSlabIncrement γ i r g (n + 1) =
      cappedSlabIncrement (pathTimeShift γ (cappedSlabExitTime γ i r g (n + 1))) i r g 0 := by
  simp only [cappedSlabIncrement, cappedSlabExitTime_succ, cappedSlabExitTime_zero,
    zero_add, pathTimeShift, ContinuousMap.coe_mk, add_zero]

/-- Conditional restart for the next increment of a regular signed realization. -/
theorem condExp_cappedSlabIncrement_regular {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (i : Fin d) (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) :
    (K x)[fun γ => cappedSlabIncrement γ i r g (n + 1) |
      cappedSlabStoppedFiltration i r g n] =ᵐ[K x]
      fun γ => ∫ η, cappedSlabIncrement η i r g 0 ∂K (γ (cappedSlabExitTime γ i r g (n + 1))) := by
  let T : Path d → ℝ≥0 := fun γ => cappedSlabExitTime γ i r g (n + 1)
  let hT := isStoppingTime_cappedSlabExitTime i r g (n + 1)
  let F : Path d → ℝ := fun η => cappedSlabIncrement η i r g 0
  have hF : StronglyMeasurable F := (measurable_cappedSlabIncrement i r g 0).stronglyMeasurable
  have hbound : ∀ η, ‖F η‖ ≤ 1 := by
    intro η
    rw [Real.norm_eq_abs, abs_le]
    exact cappedSlabIncrement_mem_Icc η i r hr g 0
  let κ := Kernel.comap K (fun γ : Path d => γ (T γ))
    (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT)
  have hFm : StronglyMeasurable[hT.measurableSpace]
      (fun γ => ∫ η, F η ∂κ γ) := by
    have hBase : StronglyMeasurable[hT.measurableSpace]
        (fun γ => ∫ η, F η ∂K (γ (T γ))) :=
      hF.integral_kernel.comp_measurable
        (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime T hT)
    simpa only [κ, Kernel.comap_apply] using hBase
  have hcond := MarkovProcess.condExp_comp_ae_eq_integral_kernel_of_restrict_map
    (K x) κ (fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ)
    (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT) hT.measurableSpace_le
    (u1_regular_signed_realization_stopping_restart hd ω lam Λ hΛ hω K hfdd x T hT)
    F hF hFm 1 hbound
  have hshift (γ : Path d) : MarkovProcess.ContinuousPath.shift (T γ) γ = pathTimeShift γ (T γ) := by
    ext t
    rfl
  simpa only [κ, Kernel.comap_apply, F, T, hshift, ← cappedSlabIncrement_succ_eq_shift,
    cappedSlabStoppedFiltration, hT]
    using hcond

end EinsteinFull.Regeneration
