import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import MarkovProcess.Trajectory.StoppingLtTop
import SubdiffusiveProcess.Processes.FellerRealizationRestart

open EinsteinRelation EinsteinRelation.SpatialDirichlet MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- The selected regular signed physical realization restarts at every finite
canonical stopping time. -/
theorem u1_regular_signed_realization_stopping_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0))) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      ((K x).restrict A).map (fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ) =
        Kernel.comap K (fun γ => γ (T γ))
          (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
            ((K x).restrict A) := by
  exact MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.realization_restrict_map_shift_stoppingTime
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
    (u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω)
    (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)
    ⟨fun _ => 0, continuous_const⟩ K hfdd x T hT

/-- Restart the supplied realization on a stopped event on which the extended
stopping time is finite. -/
theorem u1_regular_signed_extended_stopping_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (T : Path d → WithTop ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T)
    (x : Vec d) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      (∀ γ ∈ A, T γ < ⊤) →
      ((K x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((K x).restrict A) (fun γ => K (γ ((T γ).untopD 0))) := by
  intro A hA hfinite
  let D := MarkovProcess.StoppingTime.stoppingTimeSlice A T
  let Y : Path d → Vec d := fun γ => γ ((T γ).untopD 0)
  have hY : Measurable Y :=
    MarkovProcess.ContinuousPath.measurable_eval_untopD_stoppingTime T hT
  let κ := Kernel.comap K Y hY
  have hslice : ∀ n : ℕ,
      ((K x).restrict (D n)).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      κ ∘ₘ ((K x).restrict (D n)) := by
    intro n
    let S := MarkovProcess.StoppingTime.truncTime T (n : ℝ≥0)
    have hS := MarkovProcess.StoppingTime.isStoppingTime_truncTime hT (n : ℝ≥0)
    have hD : MeasurableSet (D n) :=
      MarkovProcess.StoppingTime.measurableSet_stoppingTimeSlice' hT hA n
    have hDS : MeasurableSet[hS.measurableSpace] (D n) := by
      rw [MarkovProcess.StoppingTime.measurableSpace_truncTime hT (n : ℝ≥0)]
      exact MarkovProcess.StoppingTime.measurableSet_stoppingTimeSlice hT hA n
    have hmain := u1_regular_signed_realization_stopping_restart hd ω lam Λ hΛ hω
      K hfdd x S hS (D n) hDS
    have hL : ((K x).restrict (D n)).map
        (fun γ => MarkovProcess.ContinuousPath.shift (S γ) γ) =
        ((K x).restrict (D n)).map
          (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) := by
      refine Measure.map_congr ((ae_restrict_iff' hD).mpr (ae_of_all _ fun γ hγ => ?_))
      exact congrArg (fun t => MarkovProcess.ContinuousPath.shift t γ)
        (MarkovProcess.StoppingTime.truncTime_eq_untopD_of_mem_stoppingTimeSlice hγ)
    have hR : Kernel.comap K (fun γ => γ (S γ))
        (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel S hS) ∘ₘ
        ((K x).restrict (D n)) = κ ∘ₘ ((K x).restrict (D n)) := by
      refine Measure.comp_congr ((ae_restrict_iff' hD).mpr (ae_of_all _ fun γ hγ => ?_))
      simp only [κ, Y, Kernel.comap_apply]
      change K (γ (MarkovProcess.StoppingTime.truncTime T (n : ℝ≥0) γ)) = _
      rw [MarkovProcess.StoppingTime.truncTime_eq_untopD_of_mem_stoppingTimeSlice hγ]
    rw [← hL, hmain, hR]
  have hunion : (⋃ n, D n) = A := by
    rw [MarkovProcess.StoppingTime.iUnion_stoppingTimeSlice]
    exact Set.inter_eq_left.mpr hfinite
  have h := MarkovProcess.StoppingTime.map_restrict_iUnion_eq_comp_of_forall
    (K x) κ (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ)
    (MarkovProcess.ContinuousPath.measurable_shift_untopD_stoppingTime T hT) D
    (fun n => MarkovProcess.StoppingTime.measurableSet_stoppingTimeSlice' hT hA n)
    (MarkovProcess.StoppingTime.pairwise_disjoint_stoppingTimeSlice A) hslice
  rw [hunion] at h
  simpa only [κ, Y, Kernel.coe_comap, Function.comp_def] using h


end EinsteinFull
