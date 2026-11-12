import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Integrability of the tail envelope `C * t ^ (-1 - α)` on `Ioi T`. -/
lemma flow_tail_integrableOn {C α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => C * t ^ (-1 - α)) (Set.Ioi T) volume := by
  have ha : (-1 - α : ℝ) < -1 := by linarith
  exact (integrableOn_Ioi_rpow_of_lt ha hT).const_mul C

/-- Exact value of the tail integral of the envelope `C * t ^ (-1 - α)`. -/
lemma flow_tail_integral_eq {C α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    ∫ t in Set.Ioi T, C * t ^ (-1 - α) = (C / α) * T ^ (-α) := by
  have ha : (-1 - α : ℝ) < -1 := by linarith
  rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hT,
    show (-1 - α) + 1 = -α by ring, neg_div_neg_eq]
  ring

/-- Source: `paper/main.tex:808–816`. Bochner time-tail control from the
actual integrable flow-gradient decay, in any Banach space. -/
theorem norm_integral_Ioi_le_power_decay {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) {C α T : ℝ} (hC : 0 ≤ C) (hα : 0 < α) (hT : 0 < T)
    (hgm : AEStronglyMeasurable g (volume.restrict (Set.Ioi T)))
    (hg : ∀ᵐ t ∂volume.restrict (Set.Ioi T), ‖g t‖ ≤ C * t ^ (-1 - α)) :
    IntegrableOn g (Set.Ioi T) volume ∧
      ‖∫ t in Set.Ioi T, g t‖ ≤ (C / α) * T ^ (-α) := by
  refine ⟨Integrable.mono' (flow_tail_integrableOn hα hT) hgm hg, ?_⟩
  exact (norm_integral_le_of_norm_le (flow_tail_integrableOn hα hT) hg).trans_eq
    (flow_tail_integral_eq hα hT)

/-- Source: `paper/main.tex:808–816`. The same tail controls every finite
time increment, with a constant independent of the later endpoint. -/
theorem norm_intervalIntegral_le_power_decay {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) {C α T S : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hT : 0 < T) (hTS : T ≤ S)
    (hgm : AEStronglyMeasurable g (volume.restrict (Set.Ioi T)))
    (hg : ∀ᵐ t ∂volume.restrict (Set.Ioi T), ‖g t‖ ≤ C * t ^ (-1 - α)) :
    ‖∫ t in T..S, g t‖ ≤ (C / α) * T ^ (-α) := by
  have hsub : Set.Ioc T S ⊆ Set.Ioi T := Set.Ioc_subset_Ioi_self
  have hi : IntegrableOn (fun t : ℝ => C * t ^ (-1 - α)) (Set.Ioi T) volume :=
    flow_tail_integrableOn hα hT
  have hi_Ioc : IntegrableOn (fun t : ℝ => C * t ^ (-1 - α)) (Set.Ioc T S) volume :=
    hi.mono_set hsub
  have hg_Ioc : ∀ᵐ t ∂volume.restrict (Set.Ioc T S), ‖g t‖ ≤ C * t ^ (-1 - α) :=
    ae_restrict_of_ae_restrict_of_subset hsub hg
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi T)] fun t : ℝ => C * t ^ (-1 - α) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hC (Real.rpow_nonneg (le_of_lt (lt_trans hT (Set.mem_Ioi.mp ht))) _)
  rw [intervalIntegral.integral_of_le hTS]
  calc ‖∫ t in Set.Ioc T S, g t‖ ≤ ∫ t in Set.Ioc T S, C * t ^ (-1 - α) :=
        norm_integral_le_of_norm_le hi_Ioc hg_Ioc
    _ ≤ ∫ t in Set.Ioi T, C * t ^ (-1 - α) :=
        setIntegral_mono_set hi hnonneg (Filter.Eventually.of_forall fun _ h => h.1)
    _ = (C / α) * T ^ (-α) := flow_tail_integral_eq hα hT

end EinsteinRelation.Correctors
