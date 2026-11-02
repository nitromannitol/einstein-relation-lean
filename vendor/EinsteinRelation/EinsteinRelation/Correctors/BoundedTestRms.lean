import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- A bounded test has the same bound in the normalized spatial L² norm
(`paper/main.tex:938–945`), including null-volume domains. -/
theorem scalarRms_le_of_ae_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (U : Set X) (hU : ν U ≠ ⊤) {C : ℝ} (hC : 0 ≤ C)
    {f : X → ℝ} (hf : AEStronglyMeasurable f (ν.restrict U))
    (hb : ∀ᵐ x ∂ν.restrict U, |f x| ≤ C) : scalarRms ν U f ≤ C := by
  unfold scalarRms
  -- Goal: Real.sqrt (⨍ x in U, (f x) ^ 2 ∂ν) ≤ C
  have h_sq : ∀ᵐ x ∂ν.restrict U, (f x)^2 ≤ C^2 := by
    filter_upwards [hb] with x hx
    have hx' : -C ≤ f x ∧ f x ≤ C := abs_le.mp hx
    nlinarith
  haveI : IsFiniteMeasure (ν.restrict U) :=
    isFiniteMeasure_restrict.mpr hU
  have h_int_sq : IntegrableOn (fun x => (f x)^2) U ν := by
    have h_ae : AEStronglyMeasurable (fun x => (f x)^2) (ν.restrict U) :=
      hf.pow 2
    have h_nonneg : (fun _ => (0 : ℝ)) ≤ᵐ[ν.restrict U] (fun x => (f x)^2) := by
      filter_upwards with x
      apply pow_two_nonneg
    have h_int_zero : Integrable (fun _ => (0 : ℝ)) (ν.restrict U) :=
      integrable_const (c := 0)
    have h_int_Csq : Integrable (fun _ => C^2) (ν.restrict U) :=
      integrableOn_const (C := C^2) (hs := hU)
    exact integrable_of_le_of_le h_ae h_nonneg h_sq h_int_zero h_int_Csq
  have h_int_bound : ∫ x in U, (f x)^2 ∂ν ≤ C^2 * (ν.real U) := by
    calc
      ∫ x in U, (f x)^2 ∂ν ≤ ∫ x in U, C^2 ∂ν :=
        setIntegral_mono_ae_restrict h_int_sq (integrableOn_const (C := C^2) (hs := hU)) h_sq
      _ = (ν.real U) • (C^2 : ℝ) := setIntegral_const (c := C^2)
      _ = C^2 * (ν.real U) := by rw [smul_eq_mul, mul_comm]
  rw [setAverage_eq (f := fun x => (f x)^2) (s := U)]
  -- Goal: Real.sqrt ((ν.real U)⁻¹ • ∫ x in U, (f x)^2 ∂ν) ≤ C
  by_cases hU0 : ν.real U = 0
  · rw [hU0, inv_zero, zero_smul, Real.sqrt_zero]
    exact hC
  · have hUpos : 0 < ν.real U := lt_of_le_of_ne measureReal_nonneg (Ne.symm hU0)
    have h_avg_bound : (ν.real U)⁻¹ * ∫ x in U, (f x)^2 ∂ν ≤ C^2 := by
      calc
        (ν.real U)⁻¹ * ∫ x in U, (f x)^2 ∂ν ≤ (ν.real U)⁻¹ * (C^2 * (ν.real U)) := by
          apply mul_le_mul_of_nonneg_left h_int_bound
          exact inv_nonneg.mpr measureReal_nonneg
        _ = C^2 := by field_simp [hU0]
    calc
      Real.sqrt ((ν.real U)⁻¹ • ∫ x in U, (f x)^2 ∂ν) =
          Real.sqrt ((ν.real U)⁻¹ * ∫ x in U, (f x)^2 ∂ν) := by rw [smul_eq_mul]
      _ ≤ Real.sqrt (C^2) := Real.sqrt_le_sqrt h_avg_bound
      _ = C := Real.sqrt_sq hC

end EinsteinRelation.Correctors
