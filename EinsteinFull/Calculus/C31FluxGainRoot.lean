import EinsteinFull.Calculus.C3FluxSchwartzPartitionLimit
import EinsteinFull.Calculus.C1FluxSchwartzFiniteFamily
import EinsteinFull.Calculus.C10FluxGaussianSchwartzControl
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_gain

open MeasureTheory Filter EinsteinRelation
open scoped Topology ENNReal NNReal

namespace EinsteinFull.Blueprint

/-- Assembly step for the gain root: finite partition-sum bounds for each flux component
`J j` pass to the actual Schwartz averages, and the Euclidean sum over components costs a factor
`√d`. -/
theorem c31_schwartz_average_sqrt_sum_le_of_finite_partition_bounds
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (r : ℝ) (hr : 0 < r) (ψ : SchwartzMap (Vec d) ℂ)
    (J : Fin d → Lp ℂ 2 (reducedLaw Q)) (p B : ℝ)
    (hfinite : ∀ j : Fin d, ∀ S : Finset (Fin d → ℤ),
      let b := fun z : Fin d → ℤ => centeredComplexLp Q (∫ y : Vec d,
        ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J j))
      MemLp (∑ z ∈ S, (b z : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (∑ z ∈ S, (b z : FieldPair d → ℂ))
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B) :
    (∀ j : Fin d, MemLp
      (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J j)) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)) ∧
    Real.sqrt (∑ j : Fin d, ((eLpNorm
      (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J j)) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤ Real.sqrt (d : ℝ) * B := by
  have hj := fun j : Fin d => c3_schwartz_average_lp_bound_of_finite_partition_bounds
    Q r hr ψ (J j) p B (hfinite j)
  refine ⟨fun j => (hj j).1, ?_⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  · have hB : 0 ≤ B := le_trans ENNReal.toReal_nonneg (hj ⟨0, hd⟩).2
    calc Real.sqrt (∑ j : Fin d, ((eLpNorm
          (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J j)) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2)
        ≤ Real.sqrt (∑ _j : Fin d, B ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
          exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hj j).2 2
      _ = Real.sqrt (d : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hB]

/-- Pulling a positive scalar out of finitely many `Lp` components: the Euclidean `Lp` norm sum
scales by that scalar. -/
theorem c31_sqrt_sum_eLpNorm_smul {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (a : ℝ) (ha : 0 < a) (p : ℝ≥0∞) (H G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : ∀ j, G j = (a : ℂ) • H j) (hmem : ∀ j, MemLp (H j : FieldPair d → ℂ) p (reducedLaw Q)) :
    (∀ j, MemLp (G j : FieldPair d → ℂ) p (reducedLaw Q)) ∧
    Real.sqrt (∑ j : Fin d, ((eLpNorm (G j : FieldPair d → ℂ) p (reducedLaw Q)).toReal) ^ 2) =
      a * Real.sqrt (∑ j : Fin d, ((eLpNorm (H j : FieldPair d → ℂ) p (reducedLaw Q)).toReal) ^ 2) := by
  have hae : ∀ j, (G j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] (a : ℂ) • (H j : FieldPair d → ℂ) :=
    fun j => by rw [hG j]; exact Lp.coeFn_smul _ _
  refine ⟨fun j => ((hmem j).const_smul (a : ℂ)).ae_eq (hae j).symm, ?_⟩
  have hnorm : ∀ j, (eLpNorm (G j : FieldPair d → ℂ) p (reducedLaw Q)).toReal =
      a * (eLpNorm (H j : FieldPair d → ℂ) p (reducedLaw Q)).toReal := fun j => by
    rw [eLpNorm_congr_ae (hae j), eLpNorm_const_smul, ENNReal.toReal_mul]
    simp [abs_of_pos ha]
  simp_rw [hnorm, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

/-- The stationary Schwartz average is homogeneous in the test with the reciprocal scalar. -/
theorem c31_stationarySchwartzAverage_inv_smul {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (a : ℝ) (ha : a ≠ 0) (ψ : SchwartzMap (Vec d) ℂ) (F : Lp ℂ 2 (reducedLaw Q)) :
    stationarySchwartzAverage Q ψ F =
      (a : ℂ) • stationarySchwartzAverage Q (((a : ℂ)⁻¹) • ψ) F := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  unfold stationarySchwartzAverage
  rw [← integral_smul]
  congr 1
  ext1 x
  rw [SchwartzMap.smul_apply, smul_smul, smul_eq_mul, mul_inv_cancel_left₀ ha']

/-- The consumer-facing weak-flux gain, assembled from the finite-family cutoff-Schwartz gain, the
Gaussian-derivative Schwartz control and the closed-`Lp` passage to the actual Schwartz average. -/
theorem node_l_u3A_forced_u2D_flux_u23_gain_of_deps :
    node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2 →
    node_l_u3A_forced_u2D_flux_u23_parametersStmt →
    node_e_u3A_flux_u2D_blockStmt →
    node_l_u3A_forced_u2D_flux_u23_gainStmt := by
  intro h1 h2 h3 d hd D
  obtain ⟨κ, η, η₀, ε, Clat, L, hκ, hκh, hη, hη₀, hε, hε0, hη₀0, hCl, hexp, hlat, hsch⟩ :=
    c1_flux_schwartz_finite_block_gain h1 h2 h3 d hd D
  obtain ⟨c, A, Bt, hc, hA, hBt, hctrl⟩ := c10_gaussian_derivative_normalized_test_control d D
  have hsqd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 (by omega))
  refine ⟨κ, η, η₀, ε, Clat, L, hκ, hκh, hη, hη₀, hε, hε0, hη₀0, hCl, hexp, hlat, ?_⟩
  intro p hp
  obtain ⟨growth₀, t₀, Cder, hg0, ht0, hCder, hschp⟩ := hsch p hp
  obtain ⟨ttest₀, Ctest₀, ht₀, hC₀, hmain₀⟩ := hschp c hc Bt hBt
  refine ⟨growth₀, ttest₀, fun k => Real.sqrt (d : ℝ) * Ctest₀ k * A k, hg0, ht0.trans ht₀,
    fun k => mul_pos (mul_pos hsqd (hC₀ k)) (hA k), ?_, ?_⟩
  · intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
    obtain ⟨G, J, hflux, hrest⟩ := hmain₀ Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
    refine ⟨G, J, hflux, ?_⟩
    intro t htt hζ growth K hgr hK hmem hbd s hs1 hs k dirs
    have h := hrest t htt hζ growth K hgr hK hmem hbd s hs1 k
      (((A k : ℂ)⁻¹) • unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs)
      (hctrl Q ⟨0, by omega⟩ s hs k dirs)
    have hr : 0 < (t : ℝ) ^ (1 / 2 + η) :=
      Real.rpow_pos_of_pos (by linarith [ht0.trans ht₀]) _
    obtain ⟨hmemavg, hsq⟩ := c31_schwartz_average_sqrt_sum_le_of_finite_partition_bounds Q _ hr _
      (J t) p (Ctest₀ k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) * (t : ℝ) ^ (-1 - ε) *
        s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + (t : ℝ) / s) ^ L k)
      h
    have hGeq : ∀ j : Fin d, gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) =
        (A k : ℂ) • stationarySchwartzAverage Q
          (((A k : ℂ)⁻¹) • unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs)
          (centeredComplexLp Q (J t j)) := fun j =>
      (gaussianDerivativeAverageCLM_apply hd Q s hs k dirs _).symm.trans
        (c31_stationarySchwartzAverage_inv_smul Q (A k) (hA k).ne' _ _)
    obtain ⟨hm, hn⟩ := c31_sqrt_sum_eLpNorm_smul Q (A k) (hA k) (ENNReal.ofReal p)
      (fun j => stationarySchwartzAverage Q
        (((A k : ℂ)⁻¹) • unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs)
        (centeredComplexLp Q (J t j)))
      (fun j => gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)))
      hGeq hmemavg
    refine ⟨hm, ?_⟩
    rw [hn]
    calc A k * Real.sqrt (∑ j : Fin d, ((eLpNorm (stationarySchwartzAverage Q
          (((A k : ℂ)⁻¹) • unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs)
          (centeredComplexLp Q (J t j)) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2)
        ≤ A k * (Real.sqrt (d : ℝ) * (Ctest₀ k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
          (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + (t : ℝ) / s) ^ L k)) :=
          mul_le_mul_of_nonneg_left hsq (hA k).le
      _ = _ := by ring
  · intro ctest hctest Btest hBtest
    obtain ⟨ttest₁, Ctest₁, ht₁, hC₁, hmain₁⟩ := hschp ctest hctest Btest hBtest
    refine ⟨max ttest₁ ttest₀, fun k => Real.sqrt (d : ℝ) * Ctest₁ k, le_max_right _ _,
      fun k => mul_pos hsqd (hC₁ k), ?_⟩
    intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
    obtain ⟨G, J, hflux, hrest⟩ := hmain₁ Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν
    refine ⟨G, J, hflux, ?_⟩
    intro t htt hζ growth K hgr hK hmem hbd s hs1 k ψ hψ
    have h := hrest t ((le_max_left _ _).trans htt) hζ growth K hgr hK hmem hbd s hs1 k ψ hψ
    have hr : 0 < (t : ℝ) ^ (1 / 2 + η) :=
      Real.rpow_pos_of_pos (by linarith [ht0.trans ht₀, le_max_right ttest₁ ttest₀]) _
    obtain ⟨hmemavg, hsq⟩ := c31_schwartz_average_sqrt_sum_le_of_finite_partition_bounds Q _ hr _
      (J t) p (Ctest₁ k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) * (t : ℝ) ^ (-1 - ε) *
        s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + (t : ℝ) / s) ^ L k)
      h
    exact ⟨hmemavg, hsq.trans_eq (by ring)⟩

end EinsteinFull.Blueprint
