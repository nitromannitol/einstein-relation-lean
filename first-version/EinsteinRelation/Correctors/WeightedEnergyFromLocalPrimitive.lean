import EinsteinRelation.Correctors.EnergyDissipationBound
import EinsteinRelation.Correctors.PositiveTimeDissipationIntegrability
import EinsteinRelation.Correctors.EnergyInequalityZeroEndpoint
import EinsteinRelation.Correctors.WeightedEnergyFromIntegral

/-! # Weighted energy from the actual positive-time weak primitive

Source: `paper/main.tex:824–840`. The zero trace and local energy dynamics
first imply integrability of the dissipation through zero. The integrated
inequality then extends to zero, so no integrability of the signed energy
derivative at zero is required as a premise.
-/

open MeasureTheory Set
namespace EinsteinRelation.Correctors

/-- A continuous zero trace and genuine positive-time primitives suffice
for the weighted energy maximum and total dissipation estimate.
Source: `paper/main.tex:824–840`. -/
theorem weighted_energy_bound_of_local_primitive
    {f g A E : ℝ → ℝ} {T K : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hT : 0 < T) (hK : 0 ≤ K)
    (hf : ContinuousOn f (Icc 0 T)) (hf₀ : f 0 = 0)
    (hfn : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hAn : ∀ t ∈ Icc 0 T, 0 ≤ A t)
    (hEn : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hAi : IntegrableOn (fun t => (A t)^((n : ℝ)⁻¹)) (Icc 0 T))
    (hgi : ∀ a b : ℝ, 0 < a → a < b → b ≤ T → IntegrableOn g (Ioo a b))
    (hEi : ∀ a b : ℝ, 0 < a → a < b → b ≤ T → IntegrableOn E (Ioo a b))
    (hprim : ∀ a b : ℝ, 0 < a → a < b → b ≤ T →
      (∫ s in a..b, g s) = f b - f a)
    (hine : ∀ a b : ℝ, 0 < a → a < b → b ≤ T →
      ∀ᵐ t ∂volume.restrict (Ioo a b),
        g t + E t ≤ K * ((f t)^(1 - (n : ℝ)⁻¹) * (A t)^((n : ℝ)⁻¹))) :
    IntegrableOn E (Icc 0 T) ∧
    let B := K * ∫ t in (0 : ℝ)..T, (A t)^((n : ℝ)⁻¹)
    (∀ t ∈ Icc 0 T, f t ≤ B^n) ∧ (∫ t in (0 : ℝ)..T, E t) ≤ B^n := by
  let H := fun t => K * ((f t)^(1 - (n : ℝ)⁻¹) * (A t)^((n : ℝ)⁻¹))
  have hp : 0 ≤ 1 - (n : ℝ)⁻¹ := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith [inv_le_one_of_one_le₀ h1]
  have hHi : IntegrableOn H (Icc 0 T) :=
    (IntegrableOn.continuousOn_mul
      ((Real.continuous_rpow_const hp).comp_continuousOn hf) hAi isCompact_Icc).const_mul K
  have hHn (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ H t :=
    mul_nonneg hK (mul_nonneg (Real.rpow_nonneg (hfn t ht) _) (Real.rpow_nonneg (hAn t ht) _))
  obtain ⟨C, hC⟩ := energy_dissipation_integrals_bounded hT hf hHi hHn
    (fun a ha hat => hgi a T ha hat le_rfl) (fun a ha hat => hEi a T ha hat le_rfl)
    (fun a ha hat => hprim a T ha hat le_rfl) (fun a ha hat => hine a T ha hat le_rfl)
  have hE₀ : IntegrableOn E (Icc 0 T) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    apply integrableOn_of_positive_dissipation_integrals_bounded hT _
      (fun a ha hat => hEi a T ha hat le_rfl) hC
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hEn t ⟨ht.1.le, ht.2.le⟩
  have hlocal (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ T) :
      f b - f a + (∫ s in a..b, E s) ≤ ∫ s in a..b, H s := by
    have hgi' := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr (hgi a b ha hab hb)
    have hEi' := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr (hEi a b ha hab hb)
    have hHi' := (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
      (hHi.mono_set (Icc_subset_Icc ha.le hb))
    have hle := intervalIntegral.integral_mono_ae_restrict hab.le (hgi'.add hEi') hHi' (by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact hine a b ha hab hb)
    rw [intervalIntegral.integral_add hgi' hEi', hprim a b ha hab hb] at hle
    exact hle
  have hzero := energy_inequality_from_positive_endpoints hT.le hf hE₀ hHi hlocal
  refine ⟨hE₀, ?_⟩
  simpa only [one_mul] using
    (weighted_energy_bound_of_integral_inequality n hn hT.le hK (by norm_num : (0 : ℝ) ≤ 1)
      hf hfn hAn hEn hE₀ hAi (by
        intro t ht
        have h := hzero t ht
        simpa only [hf₀, sub_zero, H, intervalIntegral.integral_const_mul, one_mul] using h))

end EinsteinRelation.Correctors
