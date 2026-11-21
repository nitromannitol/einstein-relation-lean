import EinsteinFull.External.DFGW.ResolventIntegratedScale
import EinsteinFull.External.DFGW.TimeIntegralSupremum
import EinsteinFull.External.DFGW.DynkinDyadicObservableBound

/-! # Uniform tails of integrated resolvents

The normalized reciprocal-resolvent drift term vanishes uniformly on long dyadic time grids.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The normalized partial integrated-resolvent term is uniformly negligible on long dyadic
grids. -/
theorem tendsto_measureReal_max_integrated_resolvent_dyadic
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {η | ∃ r k, k ≤ 2 ^ r ∧ δ ≤
      |(Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ) *
        ∫ u in (0 : ℝ)..(dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k : ℝ),
          transitionResolvent hP (reciprocalShift n) f (η u)|}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let F (n : ℕ) (η : C(ℝ, S)) : ℝ := (Real.sqrt (n + 1))⁻¹ *
    (reciprocalShift n : ℝ) *
      ∫ u in (0 : ℝ)..(n + 1 : ℝ), |transitionResolvent hP (reciprocalShift n) f (η u)|
  have hF := tendstoInMeasure_normalized_integrated_resolvent_abs hP f hint
  have htail := (tendstoInMeasure_iff_measureReal_norm.1 hF) δ hδ
  simp only [sub_zero, Real.norm_eq_abs] at htail
  have hdom : ∀ᵐ η ∂P, ∀ n r k : ℕ, k ≤ 2 ^ r →
      |(Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ) *
        ∫ u in (0 : ℝ)..(dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k : ℝ),
          transitionResolvent hP (reciprocalShift n) f (η u)| ≤ |F n η| := by
    apply ae_all_iff.mpr
    intro n
    have hg := (Lp.memLp (transitionResolvent hP (reciprocalShift n) f)).integrable one_le_two
    have h := ae_abs_time_integral_le_integral_abs hP
      (transitionResolvent hP (reciprocalShift n) f) hg ((n + 1 : ℕ) : ℝ≥0)
    filter_upwards [h] with η hη r k hk
    have hs := dyadicGridTime_le ((n + 1 : ℕ) : ℝ≥0) r k hk
    have hbound := hη (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k) hs
    have hc : 0 ≤ (Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ) :=
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (reciprocalShift n).2.le
    have hmul := mul_le_mul_of_nonneg_left hbound hc
    calc
      _ = ((Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ)) *
          |∫ u in (0 : ℝ)..(dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k : ℝ),
            transitionResolvent hP (reciprocalShift n) f (η u)| := by
              rw [abs_mul, abs_of_nonneg hc]
      _ ≤ F n η := by
        simpa only [F, NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one] using hmul
      _ ≤ |F n η| := le_abs_self _
  apply squeeze_zero (g := fun n : ℕ => P.real {η | δ ≤ |F n η|})
  · intro n
    exact measureReal_nonneg
  · intro n
    have hsub : {η | ∃ r k, k ≤ 2 ^ r ∧ δ ≤
        |(Real.sqrt (n + 1))⁻¹ * (reciprocalShift n : ℝ) *
          ∫ u in (0 : ℝ)..(dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k : ℝ),
            transitionResolvent hP (reciprocalShift n) f (η u)|} ≤ᵐ[P]
        {η | δ ≤ |F n η|} := by
      filter_upwards [hdom] with η hη hhit
      obtain ⟨r, k, hk, hval⟩ := hhit
      exact le_trans hval (hη n r k hk)
    exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  · exact htail

end EinsteinFull.External.DFGW
