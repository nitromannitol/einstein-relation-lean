import EinsteinFull.External.DFGW.DiffusionVarianceLimit

/-! # Diffusive scaling of the variance

The long-time normalized second-moment limit yields the corresponding limit under diffusive
scaling of the continuous version of the increment process.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

omit [BorelSpace S] in
/-- A long-time projected variance limit implies the diffusive-scaled variance limit. -/
theorem tendsto_scaled_dot_increment_sq
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (e : Vec d) (t : ℝ≥0) (D : Mat d)
    (hlim : Tendsto (fun s : ℝ => s⁻¹ * ∫ η : C(ℝ, S), dot e (X 0 s η) ^ 2 ∂P)
      atTop (𝓝 (dot e (D.mulVec e)))) :
    Tendsto (fun ε : ℝ => ∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P)
      (𝓝[>] 0) (𝓝 (dot e (D.mulVec e) * t)) := by
  by_cases ht : t = 0
  · subst t
    have hzero : (fun η => X 0 0 η) =ᵐ[P] 0 := by
      have h := compensated_zero_ae hX (fun _ => (0 : Vec d))
      simpa only [intervalIntegral.integral_same, sub_zero] using h
    have hY : ∀ᵐ η ∂P, Y η 0 = 0 := by
      filter_upwards [hX.version, hzero] with η hv hz
      exact (hv 0).trans hz
    have hzeroInt : ∀ ε : ℝ,
        (∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * 0)) ^ 2 ∂P) = 0 := by
      intro ε
      apply integral_eq_zero_of_ae
      filter_upwards [hY] with η hη
      simp only [mul_zero, hη, smul_zero, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        ]
      norm_num
    have hf : (fun ε : ℝ => ∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * 0)) ^ 2 ∂P) =
        (fun _ : ℝ => 0) := funext hzeroInt
    rw [hf]
    simpa only [NNReal.coe_zero, mul_zero] using (tendsto_const_nhds (x := (0 : ℝ)))
  · have htpos : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ht)
    have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
    have htime : Tendsto (fun ε : ℝ => ε⁻¹ ^ 2 * (t : ℝ)) (𝓝[>] 0) atTop := by
      have h := (hinv.atTop_mul_atTop₀ hinv).atTop_mul_const htpos
      simpa only [pow_two] using h
    have h := ((hlim.comp htime).mul_const (t : ℝ))
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    have htime0 : 0 ≤ ε⁻¹ ^ 2 * (t : ℝ) := mul_nonneg (sq_nonneg _) t.coe_nonneg
    have htval : (((ε⁻¹ ^ 2).toNNReal * t : ℝ≥0) : ℝ) = ε⁻¹ ^ 2 * (t : ℝ) := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)]
    have heq : (∫ η, dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 ∂P) =
        ε ^ 2 * ∫ η, dot e (X 0 (ε⁻¹ ^ 2 * (t : ℝ)) η) ^ 2 ∂P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hX.version] with η hη
      rw [hη, htval]
      have hdot (v : Vec d) : dot e (ε • v) = ε * dot e v := by
        simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hdot, mul_pow]
    rw [heq]
    dsimp only [Function.comp_apply]
    field_simp [ne_of_gt hεpos, ne_of_gt htpos]

end EinsteinFull.External.DFGW
