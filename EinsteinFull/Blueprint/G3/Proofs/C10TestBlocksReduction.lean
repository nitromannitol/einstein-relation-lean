import EinsteinFull.Blueprint.G3.Proofs.C10TestBlocks
import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_boundary
import EinsteinFull.Calculus.C8BilinearRiemann
import EinsteinFull.Calculus.C9TestBlockReplacement

/-! Exact five-dependency test-block reduction at the floored dyadic mesh. -/

noncomputable section

open EinsteinFull EinsteinRelation EinsteinRelation.External.AKM MeasureTheory ProbabilityTheory
open EinsteinRelation.Environment.AKMTestIntegralSupport

namespace EinsteinFull.Blueprint

theorem node_p_u3A_covariance_u23_test_u2D_blocks_of_deps
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hboundary : node_e_u3A_block_u2D_boundaryStmt)
    (hrate : node_e_u3A_block_u2D_cov_u2D_rateStmt)
    (hreplacement : node_p_u3A_covariance_u23_test_u2D_replacementStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt) :
    node_p_u3A_covariance_u23_test_u2D_blocksStmt := by
  intro d hd D s δ γ η β h N hN θ hθ hθ1 _ _
  have hN2 : 2 * d ≤ N := by omega
  obtain ⟨_, _, Rr, _⟩ := hreplacement d hd D s δ γ η β h N hN
  obtain ⟨Rs, hRs, hseries⟩ :=
    covarianceTestBlocks_dyadic_series hclt hjl d hd D s δ γ η β h N hN2 θ hθ
  obtain ⟨Cu, Lu, hCu, hLu, huniform⟩ :=
    covarianceTestBlocks_uniform_l2 hclt hjl d hd D s δ γ η β h N hN2
  obtain ⟨Cc, Rc, κ, hCc, hRc, hκ, hcov⟩ :=
    covarianceTestBlocks_canonical_dyadic_rate hclt hjl hrate
      d hd D s δ γ η β h N hN2 θ hθ hθ1
  obtain ⟨Cr, hCr, hriemann⟩ := bilinear_matrix_riemann_error d N hN
  obtain ⟨B, _, _, hB, _, _, hmatrix⟩ := hrate d hd D s δ γ η β h
  obtain ⟨Cp, Lp, hCp, hLp, hpair⟩ :=
    localizedPairing_testBlocks_error hclt hboundary hjl d hd D s δ γ η β h N hN
  obtain ⟨Rt, hRt⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hθ).eventually_ge_atTop (2 * max Lu Lp))
  let C := Cu + Cp + Cc + Cr * B
  let R₀ := max Rs (max Rc (max Rt (max Rr 2)))
  have hCrB : 0 ≤ Cr * B := mul_nonneg hCr.le hB.le
  have hC : 0 < C := by dsimp only [C]; positivity
  have hR₀ : 2 ≤ R₀ :=
    (le_max_right Rr 2).trans ((le_max_right Rt _).trans
      ((le_max_right Rc _).trans (le_max_right Rs _)))
  refine ⟨C, R₀, κ, hC, hR₀, hκ, ?_⟩
  intro Q hQ R hR
  have hRsR : Rs ≤ R := (le_max_left Rs _).trans hR
  have hRcR : Rc ≤ R := (le_max_left Rc _).trans ((le_max_right Rs _).trans hR)
  have hRtR : Rt ≤ R := (le_max_left Rt _).trans
    ((le_max_right Rc _).trans ((le_max_right Rs _).trans hR))
  have hR2 : 2 ≤ R := hR₀.trans hR
  let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
  have hLpos : 0 < L := by dsimp only [L]; positivity
  have hb := EinsteinFull.Calculus.S1.dyadic_scale_bounds (by linarith : 1 ≤ R) hθ rfl
  have hL : max Lu Lp ≤ L := by
    have hp := hRt R hRtR
    dsimp only [L]
    linarith [hb.2.2]
  have hLR : L ≤ R := hb.2.1.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ R) hθ1.le)
  have hs := hseries Q hQ R hRsR
  refine ⟨hs.1, ?_⟩
  intro F G
  have hm := hs.2 F G
  have hu := huniform Q hQ L ((le_max_left Lu Lp).trans hL) R hLR F
  have hp := (hpair Q hQ L ((le_max_right Lu Lp).trans hL) R hLR F).2
  have hc := hcov Q hQ R hRcR F G
  let A := covarianceDyadicLimit d hd D s δ γ η β h Q
  have hRpos : 0 < R := by linarith
  have hx (j : Fin d → ℤ) :
      R⁻¹ • covarianceTileCenter L j = covarianceTileCenter (L / R) j := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, covarianceTileCenter, div_eq_mul_inv]
    ring
  have hr := hriemann (L / R) (div_pos hLpos hRpos)
    ((div_le_one hRpos).mpr hLR) A F G
  simp_rw [← hx] at hr
  have hmat : covarianceMatrixSize A ≤ B := (hmatrix Q hQ).2.1
  have hF := EinsteinFull.Calculus.C10TestBlocks.schwartz_norm_nonneg N F
  have hG := EinsteinFull.Calculus.C10TestBlocks.schwartz_norm_nonneg N G
  have huC : Cu ≤ C := by dsimp only [C]; linarith
  have hpC : Cp ≤ C := by dsimp only [C]; linarith
  have hcC : Cc ≤ C := by dsimp only [C]; linarith
  have hrC : Cr * B ≤ C := by dsimp only [C]; linarith
  refine ⟨hm.1, hm.2.1, hm.2.2, hu.trans ?_, hp.trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right huC hF
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpC hF)
      (add_nonneg (div_nonneg hLpos.le (by linarith))
        (Real.rpow_nonneg hLpos.le _))
  · have hrB : ‖(((L / R) ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ a, ∑ b,
        F (R⁻¹ • covarianceTileCenter L j) a * (A a b : ℂ) *
          G (R⁻¹ • covarianceTileCenter L j) b -
        (∫ x, ∑ a, ∑ b, F x a * (A a b : ℂ) * G x b)‖ ≤
        (Cr * B) * schwartzTestNorm N F * schwartzTestNorm N G * (L / R) := by
      exact hr.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmat hCr.le) hF) hG)
        (div_nonneg hLpos.le hRpos.le))
    have ht := dist_triangle
      (∫ ω, covarianceTestBlocks d hd D s δ γ η β h Q R L F ω *
        covarianceTestBlocks d hd D s δ γ η β h Q R L G ω ∂reducedLaw Q)
      ((((L / R) ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ a, ∑ b,
        F (R⁻¹ • covarianceTileCenter L j) a * (A a b : ℂ) *
          G (R⁻¹ • covarianceTileCenter L j) b)
      (∫ x : Vec d, ∑ a, ∑ b, F x a * (A a b : ℂ) * G x b)
    simp only [dist_eq_norm] at ht
    apply (ht.trans (add_le_add hc hrB)).trans
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC hF) hG)
      (Real.rpow_nonneg hLpos.le (-κ))
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrC hF) hG)
      (div_nonneg hLpos.le hRpos.le)
    calc
      _ ≤ C * schwartzTestNorm N F * schwartzTestNorm N G * L ^ (-κ) +
          C * schwartzTestNorm N F * schwartzTestNorm N G * (L / R) := add_le_add h1 h2
      _ = _ := by ring

end EinsteinFull.Blueprint
