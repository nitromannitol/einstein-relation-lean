import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_closure
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_test_u2D_replacement
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_test_u2D_blocks
import EinsteinFull.Blueprint.G3.node_e_u3A_test_u2D_clt
import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_cov_u2D_rate
import EinsteinFull.Calculus.S1CovarianceL2Support
import EinsteinFull.Calculus.S1ClosureArithmeticSupport
import EinsteinFull.Work.W7.ClockCovarianceLimitProof
import EinsteinRelation.Correctors.AKMLocalCorrectorSpecialization

/-! Reduction of graph node `p:covariance#closure`, `paper/main.tex:979–984`, to
its four listed dependencies. The localization window is produced directly
from the numerical constraints (it does not need any estimate). -/

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinFull.Calculus.S1

/-- The numerical window of `e:parameters` for every structural datum. -/
theorem exists_covarianceWindow (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ s δ γ η β : ℝ, covarianceWindow d D s δ γ η β := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 5 * d / 8 + 1 / 8 := ⟨_, rfl⟩
  have hγpos : 0 < 2 * γ := by rw [hγ]; linarith
  have hη : max ((d : ℝ) / (2 * γ)) (1 / 2) < (4 / 5 : ℝ) := by
    apply max_lt
    · rw [div_lt_iff₀ hγpos, hγ]
      linarith
    · norm_num
  obtain ⟨η, hηlo, hηhi⟩ := exists_between hη
  have hη1 : (d : ℝ) / (2 * γ) < η := lt_of_le_of_lt (le_max_left _ _) hηlo
  have hη2 : (1 / 2 : ℝ) < η := lt_of_le_of_lt (le_max_right _ _) hηlo
  have hβ : η * (1 + 1 / 4) < 1 := by linarith
  obtain ⟨β, hβ1, hβ2⟩ := exists_between hβ
  refine ⟨4 / 3, 1 / 4, γ, η, β, ?_⟩
  refine ⟨Correctors.one_lt_AKMUpperEllipticity D.one_le_ellipticity, by norm_num,
    by norm_num, by norm_num, ?_, ?_, hη1, ?_, hη2, hβ1, hβ2⟩
  · rw [hγ]
    linarith
  · apply lt_min
    · rw [lt_div_iff₀ (by norm_num), hγ]
      linarith
    · rw [hγ]
      linarith
  · have e : ((1 : ℝ) + 1 / 4)⁻¹ = 4 / 5 := by norm_num
    rw [e]
    exact hηhi

theorem one_le_rpow_mul_rpow_neg {R R₀ ε : ℝ} (hR : 0 < R) (hRR : R ≤ R₀) (hε : 0 ≤ ε) :
    1 ≤ R₀ ^ ε * R ^ (-ε) := by
  rw [Real.rpow_neg hR.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hR _)]
  exact Real.rpow_le_rpow hR.le hRR hε

/-- Graph node `p:covariance#closure`, from test replacement, trimmed test blocks,
the test bound and the block covariance rate. -/
theorem node_p_u3A_covariance_u23_closure_of_deps
    (hRepl : node_p_u3A_covariance_u23_test_u2D_replacementStmt)
    (hBlocks : node_p_u3A_covariance_u23_test_u2D_blocksStmt)
    (hClt : node_e_u3A_test_u2D_cltStmt)
    (hRate : node_e_u3A_block_u2D_cov_u2D_rateStmt) :
    node_p_u3A_covariance_u23_closureStmt := by
  intro d hd D N hN
  obtain ⟨s, δ, γ, η, β, h⟩ := exists_covarianceWindow d hd D
  have hwin := h
  obtain ⟨_, _, _, hδ, hγ1, _, _, hη3, hη2, hβ1, hβ2⟩ := hwin
  obtain ⟨θ, C₁, R₁, hθ0, hθ1, hθγ, hθη, hC₁, hR₁, hrep⟩ :=
    hRepl d hd D s δ γ η β h N hN
  obtain ⟨C₂, R₂, κ, hC₂, hR₂, hκ, hblk⟩ :=
    hBlocks d hd D s δ γ η β h N hN θ hθ0 hθ1 hθγ hθη
  obtain ⟨C₃, L₃, κ₃, hC₃, hL₃, hκ₃, hrate⟩ := hRate d hd D s δ γ η β h
  obtain ⟨C₄, hC₄, hclt⟩ := hClt d hd D N hN
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hηpos : 0 < η := by linarith
  have hη1 : η < 1 := lt_trans hη3 (inv_lt_one_of_one_lt₀ (by linarith))
  have hγpos : 0 < γ := lt_trans (mul_pos (by linarith) (by linarith)) hγ1
  have hθη1 : θ * η < 1 := by nlinarith
  obtain ⟨ε, hεpos, hε1, hε2, hε3, hε4, hε5, hε6⟩ := exists_common_eps
    (2 * (1 - θ * η)) (θ * η * d - d / 2) (θ * η * γ - d / 2) (1 - θ)
    (θ * ((1 - β) / 2)) (θ * κ)
    (by linarith)
    (by
      have e : θ * η * d - d / 2 = d * (θ * η - 1 / 2) := by ring
      rw [e]
      exact mul_pos hdpos (by linarith))
    (by linarith) (by linarith) (mul_pos hθ0 (by linarith)) (mul_pos hθ0 hκ)
  have hW : 0 ≤ clockSchwartzWeightMass d N :=
    integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  obtain ⟨Cfin, hCfin⟩ : ∃ Cfin : ℝ, Cfin =
      (C₄ * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) + C₂ * (1 + 2 ^ ((1 - β) / 2))) +
        C₂ * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) + C₂ * (1 + 2 ^ ((1 - β) / 2))) +
        C₂ * (2 ^ κ + 1)) +
      (C₄ ^ 2 + C₃ * clockSchwartzWeightMass d N) * (max R₁ R₂) ^ ε + C₃ + 1 := ⟨_, rfl⟩
  have hbigpos : 0 ≤ (C₄ * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) +
        C₂ * (1 + 2 ^ ((1 - β) / 2))) +
      C₂ * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) + C₂ * (1 + 2 ^ ((1 - β) / 2))) +
      C₂ * (2 ^ κ + 1)) := by positivity
  have hsmallpos : 0 ≤ (C₄ ^ 2 + C₃ * clockSchwartzWeightMass d N) * (max R₁ R₂) ^ ε := by
    positivity
  have hCfinpos : 0 < Cfin := by rw [hCfin]; linarith
  refine ⟨ε, Cfin, hεpos, hCfinpos, ?_⟩
  intro Q hQ
  obtain ⟨hpsd, hsize, -, -⟩ := hrate Q hQ
  have hsize' : Real.sqrt (∑ a, ∑ b,
      (covarianceDyadicLimit d hd D s δ γ η β h Q a b) ^ 2) ≤ C₃ := hsize
  refine ⟨covarianceDyadicLimit d hd D s δ γ η β h Q, hpsd, ?_, ?_⟩
  · intro ξ
    refine (norm_toLp_mulVec_le _ ξ).trans ?_
    refine mul_le_mul_of_nonneg_right (hsize'.trans ?_) (norm_nonneg ξ)
    rw [hCfin]
    linarith
  · intro Z hZ R hR2 F G
    have hR1 : 1 ≤ R := by linarith
    have hnF : 0 ≤ schwartzTestNorm N F := clockSchwartz_norm_nonneg N F
    have hnG : 0 ≤ schwartzTestNorm N G := clockSchwartz_norm_nonneg N G
    have hE : 0 ≤ R ^ (-ε) := Real.rpow_nonneg (by linarith) _
    have hUFle := hclt Q hQ Z hZ R hR1 F
    have hUGle := hclt Q hQ Z hZ R hR1 G
    rcases le_or_gt (max R₁ R₂) R with hRR | hRR
    · -- large scales
      have hRR1 : R₁ ≤ R := le_trans (le_max_left _ _) hRR
      have hRR2 : R₂ ≤ R := le_trans (le_max_right _ _) hRR
      obtain ⟨hr0F, hsmF, hlocF, e1F, e2F⟩ := hrep Q hQ Z hZ R hR2 hRR1 F
      obtain ⟨hr0G, hsmG, hlocG, e1G, e2G⟩ := hrep Q hQ Z hZ R hR2 hRR1 G
      obtain ⟨-, hbF⟩ := hblk Q hQ R hRR2
      obtain ⟨-, hYF, hYG, sYF, e3F, hcov⟩ := hbF F G
      obtain ⟨-, -, -, -, e3G, -⟩ := hbF G F
      obtain ⟨hL0, hLR, hL2⟩ := dyadic_scale_bounds (R := R) (θ := θ) hR1 hθ0
        (L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)) rfl
      have hbig := closure_large_scale_bound (reducedLaw Q)
        (Lp.memLp (scaledJointPairing Q R (by linarith) Z F))
        (Lp.memLp (scaledJointPairing Q R (by linarith) Z G)) hsmF hsmG hlocF hlocG hYF hYG
        hC₁.le hC₂.le hnF hnG hR1 hL0 hLR hL2 hηpos.le hdpos.le hγpos.le hβ2.le
        hκ.le hε1 hε2 hε3 hε4 hε5 hε6 e1F e2F e3F e1G e2G e3G
        (by rw [l2Size_lp]; exact hUGle) (by exact sYF) hcov
      refine hbig.trans ?_
      have hbound : (C₄ * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) +
          C₂ * (1 + 2 ^ ((1 - β) / 2))) +
        C₂ * (C₁ * (1 + (2 ^ (η * d) + 2 ^ (η * γ))) + C₂ * (1 + 2 ^ ((1 - β) / 2))) +
        C₂ * (2 ^ κ + 1)) ≤ Cfin := by
        rw [hCfin]
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbound hnF) hnG) hE
    · -- bounded scales
      have hRpos : 0 < R := by linarith
      have hmax : 1 ≤ (max R₁ R₂) ^ ε * R ^ (-ε) :=
        one_le_rpow_mul_rpow_neg hRpos hRR.le hεpos.le
      have hNd : d < N := by omega
      have hGx : ∀ x : Vec d, ‖G x‖ ≤ schwartzTestNorm N G := fun x =>
        (le_mul_of_one_le_left (norm_nonneg _)
          (one_le_pow₀ (le_add_of_nonneg_right (Real.sqrt_nonneg _)))).trans
            (clockSchwartz_weighted_value_le N G x)
      have hT : ‖∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
          F x a * (covarianceDyadicLimit d hd D s δ γ η β h Q a b : ℂ) * G x b‖ ≤
          C₃ * schwartzTestNorm N G *
            (clockSchwartzWeightMass d N * schwartzTestNorm N F) := by
        calc ‖∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
              F x a * (covarianceDyadicLimit d hd D s δ γ η β h Q a b : ℂ) * G x b‖
            ≤ ∫ x : Vec d, ‖∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
              F x a * (covarianceDyadicLimit d hd D s δ γ η β h Q a b : ℂ) * G x b‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ x : Vec d, C₃ * schwartzTestNorm N G * ‖F x‖ := by
              refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _)
                (F.integrable.norm.const_mul _) (ae_of_all _ fun x => ?_)
              refine (norm_double_sum_le_norm _ (F x) (G x)).trans ?_
              calc Real.sqrt (∑ a, ∑ b, (covarianceDyadicLimit d hd D s δ γ η β h Q a b) ^ 2) *
                    (‖F x‖ * ‖G x‖) ≤ C₃ * (‖F x‖ * schwartzTestNorm N G) :=
                    mul_le_mul hsize' (mul_le_mul_of_nonneg_left (hGx x) (norm_nonneg _))
                      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC₃.le
                _ = C₃ * schwartzTestNorm N G * ‖F x‖ := by ring
          _ = C₃ * schwartzTestNorm N G * ∫ x : Vec d, ‖F x‖ := integral_const_mul _ _
          _ ≤ C₃ * schwartzTestNorm N G *
              (clockSchwartzWeightMass d N * schwartzTestNorm N F) :=
              mul_le_mul_of_nonneg_left (clockSchwartz_integral_norm_le hNd F)
                (mul_nonneg hC₃.le hnG)
      have hP : ‖∫ ω, scaledJointPairing Q R (by linarith) Z F ω *
            scaledJointPairing Q R (by linarith) Z G ω ∂reducedLaw Q‖ ≤
          (C₄ * schwartzTestNorm N F) * (C₄ * schwartzTestNorm N G) := by
        refine (norm_integral_mul_le_l2Size (Lp.memLp (scaledJointPairing Q R (by linarith) Z F))
          (Lp.memLp (scaledJointPairing Q R (by linarith) Z G))).trans ?_
        rw [l2Size_lp, l2Size_lp]
        exact mul_le_mul hUFle hUGle (norm_nonneg _) (by positivity)
      refine (norm_sub_le _ _).trans ?_
      have hsum : (C₄ * schwartzTestNorm N F) * (C₄ * schwartzTestNorm N G) +
          C₃ * schwartzTestNorm N G * (clockSchwartzWeightMass d N * schwartzTestNorm N F) =
          (C₄ ^ 2 + C₃ * clockSchwartzWeightMass d N) * schwartzTestNorm N F *
            schwartzTestNorm N G := by ring
      calc _ ≤ (C₄ * schwartzTestNorm N F) * (C₄ * schwartzTestNorm N G) +
            C₃ * schwartzTestNorm N G * (clockSchwartzWeightMass d N * schwartzTestNorm N F) :=
            add_le_add hP hT
        _ = (C₄ ^ 2 + C₃ * clockSchwartzWeightMass d N) * schwartzTestNorm N F *
            schwartzTestNorm N G := hsum
        _ ≤ (C₄ ^ 2 + C₃ * clockSchwartzWeightMass d N) * schwartzTestNorm N F *
            schwartzTestNorm N G * ((max R₁ R₂) ^ ε * R ^ (-ε)) :=
            le_mul_of_one_le_right (by positivity) hmax
        _ = ((C₄ ^ 2 + C₃ * clockSchwartzWeightMass d N) * (max R₁ R₂) ^ ε) *
            schwartzTestNorm N F * schwartzTestNorm N G * R ^ (-ε) := by ring
        _ ≤ Cfin * schwartzTestNorm N F * schwartzTestNorm N G * R ^ (-ε) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ?_ hnF) hnG) hE
            rw [hCfin]
            linarith

end EinsteinFull.Blueprint
