import EinsteinFull.External.DFGW.MartingaleTimeRounding

/-! # Rounding arbitrary scaled martingale times

Rounding a fixed scaled observation time to its integer part is negligible in probability.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Diffusively scaled martingale increments over a subunit rounding interval vanish in
probability as the scale tends to zero. -/
theorem tendstoInMeasure_martingale_rounding_at
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) (r : ℝ≥0) :
    TendstoInMeasure P (fun (ε : ℝ) η => ε *
      dot e (N ((ε⁻¹ ^ 2).toNNReal * r) η - N (floorTime ((ε⁻¹ ^ 2).toNNReal * r)) η))
      (𝓝[>] 0) (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  let F (ε : ℝ) (η : C(ℝ, S)) : ℝ := ε *
    dot e (N ((ε⁻¹ ^ 2).toNNReal * r) η - N (floorTime ((ε⁻¹ ^ 2).toNNReal * r)) η)
  have hF (ε : ℝ) : MemLp (F ε) 2 P := by
    have h := ((hN2 ((ε⁻¹ ^ 2).toNNReal * r)).sub
      (hN2 (floorTime ((ε⁻¹ ^ 2).toNNReal * r)))).continuousLinearMap_comp L
    simpa only [F, hL, Pi.sub_apply] using h.const_mul ε
  let q : ℝ := ∫ η, dot e (N 1 η) ^ 2 ∂P
  have hq : 0 ≤ q := integral_nonneg fun _ => sq_nonneg _
  have heq (ε : ℝ) : (∫ η, F ε η ^ 2 ∂P) = ε ^ 2 *
      ((((ε⁻¹ ^ 2).toNNReal * r) - floorTime ((ε⁻¹ ^ 2).toNNReal * r) : ℝ≥0) : ℝ) * q := by
    rw [show (fun η => F ε η ^ 2) = (fun η => ε ^ 2 *
      dot e (N ((ε⁻¹ ^ 2).toNNReal * r) η - N (floorTime ((ε⁻¹ ^ 2).toNNReal * r)) η) ^ 2) by
      funext η; simp only [F]; ring, integral_const_mul,
      integral_dot_martingale_increment_sq hP N hN hN2 hstat e
        (floorTime_le_and_sub_le_one _).1]
    simp only [q, mul_assoc]
  have hbound (ε : ℝ) : (∫ η, F ε η ^ 2 ∂P) ≤ ε ^ 2 * q := by
    rw [heq]
    have hu : ((((ε⁻¹ ^ 2).toNNReal * r) - floorTime ((ε⁻¹ ^ 2).toNNReal * r) : ℝ≥0) : ℝ) ≤ 1 := by
      simpa only [NNReal.coe_one] using
        NNReal.coe_le_coe.mpr (floorTime_le_and_sub_le_one ((ε⁻¹ ^ 2).toNNReal * r)).2
    have hmul : ((((ε⁻¹ ^ 2).toNNReal * r) - floorTime ((ε⁻¹ ^ 2).toNNReal * r) : ℝ≥0) : ℝ) * q ≤ q := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hu hq
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul (sq_nonneg ε)
  have htop : Tendsto (fun ε : ℝ => ε ^ 2 * q) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε ^ 2 * q) := by fun_prop
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using h
  have hlim : Tendsto (fun ε : ℝ => ∫ η, F ε η ^ 2 ∂P) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
      (fun _ => integral_nonneg fun _ => sq_nonneg _) hbound
  exact tendstoInMeasure_zero_of_integral_sq F hF hlim


end EinsteinFull.External.DFGW
