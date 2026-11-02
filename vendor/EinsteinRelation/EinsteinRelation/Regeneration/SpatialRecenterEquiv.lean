import EinsteinRelation.Regeneration.RegenerationShiftObservables
import EinsteinRelation.Probability.FiniteHistoryStopping

/-!
# Spatial recentering of the exact coupled histories

Source `paper/main.tex:400–402`. The coordinate change is a measurable
equivalence of the actual continuous path and bit spaces, preserves each
finite history, and commutes with deterministic time shifts.
-/

open MeasureTheory
open scoped NNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- Subtract a fixed vector from an actual continuous path. -/
def recenterPathEquiv {d : ℕ} (a : Vec d) : Path d ≃ᵐ Path d where
  toFun γ := ⟨fun t => γ t - a, γ.continuous.sub continuous_const⟩
  invFun γ := ⟨fun t => γ t + a, γ.continuous.add continuous_const⟩
  left_inv γ := by ext t i; simp
  right_inv γ := by ext t i; simp
  measurable_toFun := Probability.continuous_path_recenter.measurable.comp
    (measurable_const.prodMk measurable_id)
  measurable_invFun := by
    have h : Continuous (fun γ : Path d =>
        (⟨fun t => γ t + a, γ.continuous.add continuous_const⟩ : Path d)) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (continuous_fst.eval continuous_snd).add continuous_const
    exact h.measurable

/-- Recentering is a measurable equivalence on paths together with their unchanged bits. -/
def recenterSampleEquiv {d : ℕ} (a : Vec d) : CoupledSample d ≃ᵐ CoupledSample d :=
  (recenterPathEquiv a).prodCongr (MeasurableEquiv.refl _)

@[simp] theorem recenterSampleEquiv_apply {d : ℕ} (a : Vec d) (z : CoupledSample d) :
    recenterSampleEquiv a z = recenterSample a z := rfl

/-- Stopping the exact finite history commutes with spatial recentering. -/
theorem stoppedHistorySample_recenter {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (a : Vec d) (z : CoupledSample d) :
    Probability.stoppedHistorySample Δ n (recenterSample a z) =
      recenterSample a (Probability.stoppedHistorySample Δ n z) := rfl

/-- A finite-history test remains a finite-history test after recentering. -/
theorem measurable_finiteHistory_comp_recenter {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (a : Vec d) {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (F : CoupledSample d → E)
    (hF : @Measurable (CoupledSample d) E (finiteHistorySigma Δ n) inferInstance F) :
    @Measurable (CoupledSample d) E (finiteHistorySigma Δ n) inferInstance
      (fun z => F (recenterSample a z)) := by
  have hf : Measurable F := hF.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
  have h : @Measurable (CoupledSample d) E (finiteHistorySigma Δ n) inferInstance
      (fun z => F (recenterSample a (Probability.stoppedHistorySample Δ n z))) :=
    (hf.comp (recenterSampleEquiv a).measurable).comp (Probability.measurable_stoppedHistorySample Δ n)
  simpa only [← stoppedHistorySample_recenter,
    Probability.finiteHistory_test_stopped Δ n F hF] using h

/-- The absolute path shift commutes with the fixed spatial coordinate change. -/
theorem sampleTimeShift_recenter {d : ℕ} (Δ : ℝ≥0) (a : Vec d)
    (z : CoupledSample d) (t : ℝ≥0) :
    sampleTimeShift Δ (recenterSample a z) t = recenterSample a (sampleTimeShift Δ z t) := rfl


end EinsteinRelation.Regeneration
