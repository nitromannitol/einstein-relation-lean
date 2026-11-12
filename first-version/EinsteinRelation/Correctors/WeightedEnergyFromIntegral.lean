import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! # Weighted energy from an integrated weak inequality

Source: `paper/main.tex:832–848`. Taking the maximum of the continuous
energy gives the same estimate, up to a constant depending on the integer
power, without differentiating that energy. The weak PDE must still supply
the integrated inequality.
-/

open MeasureTheory Set

namespace EinsteinRelation.Correctors

/-- The integrated weighted energy inequality controls both the maximum
energy and its dissipation. The power of `K` absorbs the harmless loss
relative to the epsilon-regularized classical argument.
Source: `paper/main.tex:839–848`. -/
theorem weighted_energy_bound_of_integral_inequality
    {f A E : ℝ → ℝ} {T K c : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hf : ContinuousOn f (Icc 0 T))
    (hfn : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hAn : ∀ t ∈ Icc 0 T, 0 ≤ A t)
    (hEn : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (_hEi : IntegrableOn E (Icc 0 T))
    (hAi : IntegrableOn (fun t => (A t)^((n : ℝ)⁻¹)) (Icc 0 T))
    (hine : ∀ t ∈ Icc 0 T,
      f t + c * (∫ s in (0 : ℝ)..t, E s) ≤
        K * ∫ s in (0 : ℝ)..t, (f s)^(1 - (n : ℝ)⁻¹) * (A s)^((n : ℝ)⁻¹)) :
    let B := K * ∫ t in (0 : ℝ)..T, (A t)^((n : ℝ)⁻¹)
    (∀ t ∈ Icc 0 T, f t ≤ B^n) ∧
      c * (∫ t in (0 : ℝ)..T, E t) ≤ B^n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn0 : n ≠ 0 := by omega
  have hq : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hp : 0 ≤ 1 - (n : ℝ)⁻¹ := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith [inv_le_one_of_one_le₀ this]
  intro B
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hT⟩ hf
  let S := f t₀
  have hS : 0 ≤ S := hfn t₀ ht₀
  have hSp : 0 ≤ S^(1 - (n : ℝ)⁻¹) := Real.rpow_nonneg hS _
  have hIc : IntervalIntegrable (fun t => (A t)^((n : ℝ)⁻¹)) volume 0 T :=
    IntegrableOn.intervalIntegrable (by rwa [uIcc_of_le hT])
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..T, (A t)^((n : ℝ)⁻¹) :=
    intervalIntegral.integral_nonneg hT fun t ht => Real.rpow_nonneg (hAn t ht) _
  have hB : 0 ≤ B := mul_nonneg hK hI0
  have hpowc : ContinuousOn (fun t => (f t)^(1 - (n : ℝ)⁻¹)) (Icc 0 T) :=
    (Real.continuous_rpow_const hp).comp_continuousOn hf
  have hprod : IntegrableOn
      (fun t => (f t)^(1 - (n : ℝ)⁻¹) * (A t)^((n : ℝ)⁻¹)) (Icc 0 T) :=
    IntegrableOn.continuousOn_mul hpowc hAi isCompact_Icc
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      K * (∫ s in (0 : ℝ)..t, (f s)^(1 - (n : ℝ)⁻¹) * (A s)^((n : ℝ)⁻¹)) ≤
        S^(1 - (n : ℝ)⁻¹) * B := by
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hpi : IntervalIntegrable
        (fun s => (f s)^(1 - (n : ℝ)⁻¹) * (A s)^((n : ℝ)⁻¹)) volume 0 t :=
      IntegrableOn.intervalIntegrable (by rw [uIcc_of_le ht.1]; exact hprod.mono_set hsub)
    have hai : IntervalIntegrable (fun s => (A s)^((n : ℝ)⁻¹)) volume 0 t :=
      IntegrableOn.intervalIntegrable (by rw [uIcc_of_le ht.1]; exact hAi.mono_set hsub)
    have hm : (∫ s in (0 : ℝ)..t, (f s)^(1 - (n : ℝ)⁻¹) * (A s)^((n : ℝ)⁻¹)) ≤
        S^(1 - (n : ℝ)⁻¹) * (∫ s in (0 : ℝ)..t, (A s)^((n : ℝ)⁻¹)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on ht.1 hpi (hai.const_mul _)
      intro s hs
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hfn s (hsub hs)) (hmax (hsub hs)) hp)
        (Real.rpow_nonneg (hAn s (hsub hs)) _)
    have hIt : (∫ s in (0 : ℝ)..t, (A s)^((n : ℝ)⁻¹)) ≤
        ∫ s in (0 : ℝ)..T, (A s)^((n : ℝ)⁻¹) :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
          Real.rpow_nonneg (hAn s ⟨hs.1.le, hs.2⟩) _) hIc
    calc
      _ ≤ K * (S^(1 - (n : ℝ)⁻¹) * (∫ s in (0 : ℝ)..t, (A s)^((n : ℝ)⁻¹))) :=
        mul_le_mul_of_nonneg_left hm hK
      _ ≤ K * (S^(1 - (n : ℝ)⁻¹) * (∫ s in (0 : ℝ)..T, (A s)^((n : ℝ)⁻¹))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIt hSp) hK
      _ = S^(1 - (n : ℝ)⁻¹) * B := by dsimp only [B]; ring
  have hSineq : S ≤ S^(1 - (n : ℝ)⁻¹) * B := by
    have hE0 : 0 ≤ c * (∫ s in (0 : ℝ)..t₀, E s) :=
      mul_nonneg hc (intervalIntegral.integral_nonneg ht₀.1 fun s hs =>
        hEn s ⟨hs.1, hs.2.trans ht₀.2⟩)
    linarith [hine t₀ ht₀, hbound t₀ ht₀]
  have hSq : S^((n : ℝ)⁻¹) ≤ B := by
    rcases eq_or_lt_of_le hS with hzero | hpos
    · simp [← hzero, Real.zero_rpow hq.ne', hB]
    · have hsplit : S = S^(1 - (n : ℝ)⁻¹) * S^((n : ℝ)⁻¹) := by
        rw [← Real.rpow_add hpos]
        simp
      exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hpos _)).mp
        (hsplit.symm.le.trans hSineq)
  have hSn : S ≤ B^n := by
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hS _) hSq n
    rwa [Real.rpow_inv_natCast_pow hS hn0] at hpow
  have hSnq : S^(1 - (n : ℝ)⁻¹) * B ≤ B^n := by
    have hmono := Real.rpow_le_rpow hS hSn hp
    have hsplit : (B^n)^(1 - (n : ℝ)⁻¹) * (B^n)^((n : ℝ)⁻¹) = B^n := by
      rw [← Real.rpow_add' (pow_nonneg hB n) (by simp :
        (1 - (n : ℝ)⁻¹) + (n : ℝ)⁻¹ ≠ 0)]
      simp
    rw [Real.pow_rpow_inv_natCast hB hn0] at hsplit
    exact (mul_le_mul_of_nonneg_right hmono hB).trans hsplit.le
  refine ⟨fun t ht => (hmax ht).trans hSn, ?_⟩
  have hlast := (hine T ⟨hT, le_rfl⟩).trans (hbound T ⟨hT, le_rfl⟩)
  linarith [hSnq, hfn T ⟨hT, le_rfl⟩]

end EinsteinRelation.Correctors
