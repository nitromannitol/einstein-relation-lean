import EinsteinFull.External.DFGW.DFGWMartingaleApproximation

/-! # Diffusively scaled martingale remainder

The fixed-time mean-square remainder in the martingale approximation vanishes under diffusive
scaling of the continuous increment version.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- A sublinear fixed-time mean-square remainder vanishes under diffusive scaling. -/
theorem tendsto_scaled_martingale_remainder_sq
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (N : ℝ≥0 → C(ℝ, S) → Vec d)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d)
    (hrem : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ η, (dot e (X 0 t η) - dot e (N t η)) ^ 2 ∂P) atTop (𝓝 0)) (t : ℝ≥0) :
    Tendsto (fun ε : ℝ => ∫ η,
      (dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) -
        ε * dot e (N ((ε⁻¹ ^ 2).toNNReal * t) η)) ^ 2 ∂P)
      (𝓝[>] 0) (𝓝 0) := by
  have hNzero : N 0 =ᵐ[P] 0 := by
    have hshift (η : C(ℝ, S)) : Draft.dfgwShift 0 η = η := by
      ext u
      simp [Draft.dfgwShift]
    filter_upwards [hstat 0 0] with η hη
    simp only [zero_add, NNReal.coe_zero, hshift, Pi.zero_apply] at hη ⊢
    have hη' : N 0 η - N 0 η = N 0 η := hη
    simpa only [sub_self] using hη'.symm
  by_cases ht : t = 0
  · subst t
    have hXzero : (fun η => X 0 0 η) =ᵐ[P] 0 := by
      have h := compensated_zero_ae hX (fun _ => (0 : Vec d))
      simpa only [intervalIntegral.integral_same, sub_zero] using h
    have hYzero : ∀ᵐ η ∂P, Y η 0 = 0 := by
      filter_upwards [hX.version, hXzero] with η hv hz
      exact (hv 0).trans hz
    have hzero (ε : ℝ) : (∫ η,
        (dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * 0)) -
          ε * dot e (N ((ε⁻¹ ^ 2).toNNReal * 0) η)) ^ 2 ∂P) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hYzero, hNzero] with η hy hn
      simp [hy, hn, dot]
    simp_rw [hzero]
    exact tendsto_const_nhds
  · have htpos : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ht)
    have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
    have htimeR : Tendsto (fun ε : ℝ => ε⁻¹ ^ 2 * (t : ℝ)) (𝓝[>] 0) atTop := by
      have h := (hinv.atTop_mul_atTop₀ hinv).atTop_mul_const htpos
      simpa only [pow_two] using h
    have htime : Tendsto (fun ε : ℝ => (ε⁻¹ ^ 2).toNNReal * t) (𝓝[>] 0) atTop := by
      apply NNReal.tendsto_coe_atTop.mp
      convert htimeR using 1
      funext ε
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)]
    have h := (hrem.comp htime).mul_const (t : ℝ)
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    have htval : (((ε⁻¹ ^ 2).toNNReal * t : ℝ≥0) : ℝ) = ε⁻¹ ^ 2 * (t : ℝ) := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)]
    have hdot (v : Vec d) : dot e (ε • v) = ε * dot e v := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have heq : (∫ η, (dot e (ε • Y η ((ε⁻¹ ^ 2).toNNReal * t)) -
        ε * dot e (N ((ε⁻¹ ^ 2).toNNReal * t) η)) ^ 2 ∂P) =
        ε ^ 2 * ∫ η, (dot e (X 0 (ε⁻¹ ^ 2 * (t : ℝ)) η) -
          dot e (N ((ε⁻¹ ^ 2).toNNReal * t) η)) ^ 2 ∂P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hX.version] with η hη
      rw [hη, htval, hdot]
      ring
    rw [heq]
    dsimp only [Function.comp_apply]
    rw [htval]
    field_simp [ne_of_gt hεpos, ne_of_gt htpos]

end EinsteinFull.External.DFGW
