import EinsteinRelation.Correctors.PairedEnergyProbability
import EinsteinRelation.Correctors.PairedDecayIntegralComparison

/-! # The sharp scale from paired scalar decay

Source: `paper/main.tex:844–857`. The scalar moment majorant is integrated
at its natural exponent before the scale `T = 4 R²` is substituted. The
constant is chosen before the probability space, field, and radius.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Paired weighted energy and the scalar decay profile give the sharp
`R^(-d/2)` probability moment bound. This internal assembly consumes the
samplewise energy and time Cauchy--Schwarz estimates without postulating
any paired corrector conclusion. Source: `paper/main.tex:844–857`. -/
theorem paired_energy_moment_decay (d n : ℕ) (hd : 2 ≤ d)
    (hn : 1 + (d : ℝ)/2 < (n : ℝ)) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 < B ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (Q : Measure Ω) [IsProbabilityMeasure Q] (p : ℝ), 2 ≤ p → ∀ (R : ℝ), 1 ≤ R →
      ∀ (H : ℝ → ℝ), Measurable H → (∀ t, 0 ≤ H t) →
      (∀ t, 0 ≤ t → H t ≤ M * (1+t)^(-(1 : ℝ)/2-(d : ℝ)/4)) →
      ∀ (a : ℝ × Ω → ℝ), Measurable a → (∀ z, 0 ≤ a z) →
      (∀ t, 0 < t → MemLp (fun ω => a (t,ω)) (ENNReal.ofReal p) Q ∧
        eLpNorm (fun ω => a (t,ω)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (H t)) →
      ∀ (F E : Ω → ℝ), Measurable F → (∀ ω, 0 ≤ F ω) →
      (∀ᵐ ω ∂Q, 0 ≤ E ω) →
      (∀ᵐ ω ∂Q, E ω ≤ (C / R^2 *
        ∫ t in Icc (0 : ℝ) (4*R^2), (a (t,ω))^(2/(n : ℝ)))^n) →
      (∀ᵐ ω ∂Q, (F ω)^2 ≤ (4*R^2) * E ω) →
      MemLp F (ENNReal.ofReal p) Q ∧
        eLpNorm F (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (B * R^(-(d : ℝ)/2)) := by
  obtain ⟨B₀, hB₀, hdecay⟩ := paired_decay_integral_comparison d n hd hn (M^(2/(n : ℝ))) (Real.rpow_nonneg hM _)
  refine ⟨(Real.sqrt C)^n * B₀ + 1, by positivity, ?_⟩
  intro Ω _ Q _ p hp R hR H hHm hH hbound a ha han hmom F E hFm hFn hEn henergy hcs
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hT : 0 ≤ 4*R^2 := by positivity
  have hn2 : 2 ≤ n := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hn' : (2 : ℝ) < n := by linarith
    exact_mod_cast hn'.le
  have hq : 0 ≤ 2/(n : ℝ) := by positivity
  have hprofile : Measurable (fun t => H t^(2/(n : ℝ))) := hHm.pow_const _
  have hprofileBound (t : ℝ) (ht : 0 ≤ t) :
      H t^(2/(n : ℝ)) ≤ M^(2/(n : ℝ)) * (1+t)^(-(1+(d : ℝ)/2)/(n : ℝ)) := by
    have ht0 : 0 ≤ 1+t := by linarith
    calc
      H t^(2/(n : ℝ)) ≤ (M * (1+t)^(-(1 : ℝ)/2-(d : ℝ)/4))^(2/(n : ℝ)) :=
        Real.rpow_le_rpow (hH t) (hbound t ht) hq
      _ = _ := by
        rw [Real.mul_rpow hM (Real.rpow_nonneg ht0 _), ← Real.rpow_mul ht0]
        congr 2
        ring
  have hprofileInt : IntegrableOn (fun t => H t^(2/(n : ℝ))) (Icc 0 (4*R^2)) := by
    have hw : ContinuousOn (fun t : ℝ => M^(2/(n : ℝ)) * (1+t)^(-(1+(d : ℝ)/2)/(n : ℝ)))
        (Icc 0 (4*R^2)) := by
      have hb : ContinuousOn (fun t : ℝ => (1+t)^(-(1+(d : ℝ)/2)/(n : ℝ)))
          (Icc 0 (4*R^2)) := by
        have hbase : ContinuousOn (fun t : ℝ => 1+t) (Icc 0 (4*R^2)) := by fun_prop
        exact hbase.rpow_const (fun t ht => Or.inl (ne_of_gt (by linarith [ht.1])))
      exact continuousOn_const.mul hb
    exact (hw.integrableOn_Icc).mono' hprofile.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hH t) _)]
      exact hprofileBound t ht.1)
  let aPos : ℝ × Ω → ℝ := (Prod.fst ⁻¹' Ioi 0).indicator a
  have haPos : Measurable aPos := ha.indicator (measurableSet_Ioi.preimage measurable_fst)
  have hapos (z : ℝ × Ω) : 0 ≤ aPos z := by
    by_cases hz : 0 < z.1
    · simpa [aPos, hz] using han z
    · simp [aPos, hz]
  have hposmom (t : ℝ) : MemLp (fun ω => aPos (t,ω)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => aPos (t,ω)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (H t) := by
    by_cases ht : 0 < t
    · simpa [aPos, ht] using hmom t ht
    · simp only [aPos, Set.indicator, Set.mem_preimage, Set.mem_Ioi, if_neg ht]
      exact ⟨MemLp.zero, by simp⟩
  have haposInt (ω : Ω) : (∫ t in Icc (0 : ℝ) (4*R^2), (aPos (t,ω))^(2/(n : ℝ))) =
      ∫ t in Icc (0 : ℝ) (4*R^2), (a (t,ω))^(2/(n : ℝ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht hne
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hne)
    simp [aPos, ht0]
  have henergyPos : ∀ᵐ ω ∂Q, E ω ≤ (C / R^2 *
      ∫ t in Icc (0 : ℝ) (4*R^2), (aPos (t,ω))^(2/(n : ℝ)))^n := by
    simpa only [haposInt] using henergy
  obtain ⟨hmem, hnorm⟩ := paired_energy_moment_le Q (volume.restrict (Icc 0 (4*R^2)))
    hp hn2 hC hR0 hT H hHm hH hprofileInt
    aPos haPos hapos hposmom F E hFm hFn hEn henergyPos hcs
  refine ⟨hmem, hnorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hscale := hdecay (fun t => H t^(2/(n : ℝ))) hprofile
    (fun t _ => Real.rpow_nonneg (hH t) _) hprofileBound R hR
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at hscale
  have hfactor := mul_le_mul_of_nonneg_left hscale (pow_nonneg (Real.sqrt_nonneg C) n)
  have hr : 0 ≤ R^(-(d : ℝ)/2) := Real.rpow_nonneg hR0.le _
  nlinarith only [hfactor, hr]

end EinsteinRelation.Correctors
