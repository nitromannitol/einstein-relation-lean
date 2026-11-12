import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Compact smooth test normalization; source `paper/main.tex:808–816`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors


theorem smooth_test_sub_unit_mean {a b : ℝ}
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcρ : HasCompactSupport ρ)
    (hcη : HasCompactSupport η) (hsρ : tsupport ρ ⊆ Set.Ioo a b)
    (hsη : tsupport η ⊆ Set.Ioo a b) (hρ1 : (∫ t : ℝ, ρ t) = 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => η t - (∫ s : ℝ, η s) * ρ t) ∧
      HasCompactSupport (fun t => η t - (∫ s : ℝ, η s) * ρ t) ∧
      tsupport (fun t => η t - (∫ s : ℝ, η s) * ρ t) ⊆ Set.Ioo a b ∧
      (∫ t : ℝ, η t - (∫ s : ℝ, η s) * ρ t) = 0 := by
  set c := (∫ s : ℝ, η s) with hc_def
  have hη_cont : Continuous η := hη.continuous
  have hρ_cont : Continuous ρ := hρ.continuous
  have h_int_η : Integrable η := hη_cont.integrable_of_hasCompactSupport hcη
  have h_int_ρ : Integrable ρ := hρ_cont.integrable_of_hasCompactSupport hcρ
  have h_int_cρ : Integrable (fun t => c * ρ t) :=
    h_int_ρ.const_mul c
  have hc_cont : ContDiff ℝ (⊤ : ℕ∞) (fun t => c * ρ t) :=
    (contDiff_const (c := c)).mul hρ
  have hc_comp : HasCompactSupport (fun t => c * ρ t) := by
    simpa [mul_comm] using hcρ.mul_right (f' := fun _ => c)
  have hc_tsupp : tsupport (fun t => c * ρ t) ⊆ Set.Ioo a b :=
    (tsupport_mul_subset_right (f := fun _ => c) (g := ρ)).trans hsρ
  have h_main_cont : ContDiff ℝ (⊤ : ℕ∞) (fun t => η t - c * ρ t) :=
    hη.sub hc_cont
  have h_main_comp : HasCompactSupport (fun t => η t - c * ρ t) :=
    hcη.sub hc_comp
  have h_main_tsupp : tsupport (fun t => η t - c * ρ t) ⊆ Set.Ioo a b :=
    (tsupport_sub η (fun t => c * ρ t)).trans (Set.union_subset hsη hc_tsupp)
  have h_main_int : (∫ t : ℝ, η t - c * ρ t) = 0 := by
    calc
      (∫ t : ℝ, η t - c * ρ t) = (∫ t : ℝ, η t) - (∫ t : ℝ, c * ρ t) :=
        integral_sub h_int_η h_int_cρ
      _ = (∫ t : ℝ, η t) - c * (∫ t : ℝ, ρ t) := by rw [integral_const_mul c ρ]
      _ = (∫ t : ℝ, η t) - c * 1 := by rw [hρ1]
      _ = (∫ t : ℝ, η t) - c := by ring
      _ = 0 := by
        dsimp [c]
        ring
  simpa [hc_def] using ⟨h_main_cont, h_main_comp, h_main_tsupp, h_main_int⟩

end EinsteinRelation.Correctors
