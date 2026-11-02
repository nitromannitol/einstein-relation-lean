import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_test_u2D_blocks
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_test_u2D_replacement
import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_cov_u2D_rate
import EinsteinFull.Blueprint.G3.Proofs.S1BlockRecursion
import EinsteinFull.Calculus.C10TestBlocksSupport
import EinsteinFull.Calculus.S1ClosureArithmeticSupport

/-! Ingredients for the literal infinite-lattice test-block reduction. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinFull.Calculus.S1 EinsteinFull.Calculus.C10TestBlocks

/-- All trimmed lattice blocks are jointly independent above a structural
threshold. The threshold is chosen before the environment law. -/
theorem covarianceTestBlocks_children_independent
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ L : ℝ, L₀ ≤ L →
        iIndepFun (fun j : Fin d → ℤ =>
          covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
            (covarianceTileCenter L j) (fun _ => 1)) (reducedLaw Q) := by
  have hwin := h
  obtain ⟨_, _, _, hδ, _, _, _, _, hη2, hβ1, _⟩ := hwin
  have hη : 0 < η := by linarith
  have hβη : η < β := by nlinarith [mul_pos hη hδ]
  obtain ⟨L₁, hL₁, hthr⟩ := recursion_thresholds D.one_le_dependenceRange hδ hη hβη hβ1
  refine ⟨max L₁ 2, le_max_right _ _, ?_⟩
  intro Q hQ L hL
  haveI := reducedLaw_probability Q
  have hLL : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ L := le_trans (by norm_num) ((le_max_right L₁ 2).trans hL)
  obtain ⟨hr, _, hsep⟩ := hthr L hLL
  have hfield := cov_lsf hjl d hd D s δ γ η β h Q hQ (L ^ η) hr
  have hind := lattice_blocks_iIndepFun (reducedLaw_hasFiniteRange Q)
    (ρ := covarianceLocalizationRadius D δ (L ^ η))
    (fun _ _ hz => hz) hfield (reducedLaw_hT Q)
    (L ^ (-(d : ℝ) / 2)) hL0 hsep
  convert hind using 1 <;> funext j ω a
  simp only [covarianceBlock, covF, one_mul]

/-- The prescribed dyadic mesh eventually exceeds the structural independence
threshold, uniformly in the environment law. -/
theorem covarianceTestBlocks_dyadic_children_independent
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ R : ℝ, R₀ ≤ R →
        let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
        iIndepFun (fun j : Fin d → ℤ =>
          covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
            (covarianceTileCenter L j) (fun _ => 1)) (reducedLaw Q) := by
  obtain ⟨L₀, _, hind⟩ := covarianceTestBlocks_children_independent hjl d hd D s δ γ η β h
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hθ).eventually_ge_atTop (2 * L₀))
  refine ⟨max R₁ 2, le_max_right _ _, ?_⟩
  intro Q hQ R hR
  have hR2 : 2 ≤ R := (le_max_right R₁ 2).trans hR
  have hp := hR₁ R ((le_max_left _ _).trans hR)
  have hb := dyadic_scale_bounds (by linarith : 1 ≤ R) hθ rfl
  exact hind Q hQ _ (by linarith [hb.2.2])

/-- Each trimmed lattice block has the centered origin block's actual law. -/
theorem covarianceTestBlocks_child_identDistrib
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (L : ℝ) (hr : 2 * D.dependenceRange ≤ L ^ η) (j : Fin d → ℤ) :
    IdentDistrib
      (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
        (covarianceTileCenter L j) (fun _ => 1))
      (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β) 0 (fun _ => 1))
      (reducedLaw Q) (reducedLaw Q) := by
  haveI := reducedLaw_probability Q
  exact blk_identDistrib (cov_lsf hjl d hd D s δ γ η β h Q hQ (L ^ η) hr)
    (reducedLaw_hT Q) _ _ _

/-- Every coordinate of every trimmed block is integrable and centered. -/
theorem covarianceTestBlocks_child_integrable_mean
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (L : ℝ) (hr : 2 * D.dependenceRange ≤ L ^ η)
    (j : Fin d → ℤ) (a : JointObservationIndex d) :
    let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
      (covarianceTileCenter L j) (fun _ => 1)
    Integrable (fun ω => X ω a) (reducedLaw Q) ∧
      (∫ ω, X ω a ∂reducedLaw Q) = 0 := by
  haveI := reducedLaw_probability Q
  exact blk_integrable_mean (cov_lsf hjl d hd D s δ γ η β h Q hQ (L ^ η) hr)
    (reducedLaw_hT Q) _ (volume_clockBlockCube_lt_top _ _) a

/-- A uniform Euclidean L² bound for every trimmed block in the infinite tiling.
No square-integrability is inferred from a totalized second-moment integral. -/
theorem covarianceTestBlocks_children_l2
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ L : ℝ, L₀ ≤ L → ∀ j : Fin d → ℤ,
        let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
          (covarianceTileCenter L j) (fun _ => 1)
        L2Vec (reducedLaw Q) X ∧ covarianceL2Size (reducedLaw Q) X ≤ C := by
  have hwin := h
  obtain ⟨_, _, _, hδ, _, _, _, hηupper, hηlower, _, _⟩ := hwin
  have hη : 0 < η := by linarith
  have hη1 : η < 1 := hηupper.trans (inv_lt_one_of_one_lt₀ (by linarith))
  obtain ⟨C, Lc, hC, hLc, hdata⟩ := cov_clt_data hclt d hd D s δ γ η β h
  obtain ⟨Lm, hLm⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually_ge_atTop (2 * D.dependenceRange))
  refine ⟨C, max Lc Lm, hC, hLc.trans (le_max_left _ _), ?_⟩
  intro Q hQ L hL j
  haveI := reducedLaw_probability Q
  have hLcL : Lc ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := le_trans (by linarith) (hLc.trans hLcL)
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hr := hLm L ((le_max_right _ _).trans hL)
  have hfield := cov_lsf hjl d hd D s δ γ η β h Q hQ (L ^ η) hr
  have hscale : L ^ η ≤ L :=
    (Real.rpow_le_rpow_of_exponent_le hL1 hη1.le).trans_eq (Real.rpow_one L)
  obtain ⟨hL2, hbound⟩ := (hdata Q hQ L hLcL (L ^ η) le_rfl hscale hfield).2
    (L ^ β) (Real.rpow_nonneg hL0 _)
  have hid := covarianceTestBlocks_child_identDistrib hjl d hd D s δ γ η β h Q hQ L hr j
  refine ⟨blk_L2Vec_of_identDistrib hfield (reducedLaw_hT Q) _ _ _ hid hL2, ?_⟩
  have he := (hid.comp (u := fun v : JointObservationIndex d → ℝ => vsize v ^ 2)
    ((measurable_vsize (ι := JointObservationIndex d)).pow_const 2)).integral_eq
  exact (congrArg Real.sqrt he).trans_le hbound

/-- The literal infinite trimmed-block sum is a.e. absolutely summable and
square-integrable for every Schwartz test, above a structural mesh threshold.
The order N remains the original one. -/
theorem covarianceTestBlocks_summable_memLp
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : 2 * d ≤ N) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ L : ℝ, L₀ ≤ L → ∀ R : ℝ, 0 < R →
        ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        let X := fun j : Fin d → ℤ =>
          covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
            (covarianceTileCenter L j) (fun _ => 1)
        (∀ᵐ ω ∂reducedLaw Q, Summable (fun j =>
          ∑ a, F (R⁻¹ • covarianceTileCenter L j) a * (X j ω a : ℂ))) ∧
          MemLp (covarianceTestBlocks d hd D s δ γ η β h Q R L F) 2
            (reducedLaw Q) := by
  have hwin := h
  obtain ⟨_, _, _, _, _, _, _, _, hηlower, _, _⟩ := hwin
  have hη : 0 < η := by linarith
  obtain ⟨C, Lc, _, hLc, hdata⟩ :=
    covarianceTestBlocks_children_l2 hclt hjl d hd D s δ γ η β h
  obtain ⟨Lm, hLm⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually_ge_atTop (2 * D.dependenceRange))
  refine ⟨max Lc Lm, hLc.trans (le_max_left _ _), ?_⟩
  intro Q hQ L hL R hR F
  let X := fun j : Fin d → ℤ =>
    covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
      (covarianceTileCenter L j) (fun _ => 1)
  have hLcL := (le_max_left Lc Lm).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < Lc) hLcL
  have hr := hLm L ((le_max_right _ _).trans hL)
  have hX : ∀ j a, MemLp (fun ω => X j ω a) 2 (reducedLaw Q) :=
    fun j a => (hdata Q hQ L hLcL j).1.coord_memLp a
  let c := fun a => eLpNorm (fun ω => X 0 ω a) 2 (reducedLaw Q)
  have hc : ∀ a, c a ≠ ⊤ := fun a => (hX 0 a).ne
  have hb : ∀ j a, eLpNorm (fun ω => X j ω a) 2 (reducedLaw Q) ≤ c a := by
    intro j a
    have hid := covarianceTestBlocks_child_identDistrib hjl d hd D s δ γ η β h
      Q hQ L hr j
    have he := (hid.comp (measurable_pi_apply a)).eLpNorm_eq 2
    have hz : covarianceTileCenter L (0 : Fin d → ℤ) = 0 := by
      funext i
      simp only [covarianceTileCenter, Pi.zero_apply, Int.cast_zero, mul_zero]
    dsimp only [c, X]
    rw [hz]
    exact he.le
  have hgrid : ∀ j : Fin d → ℤ,
      R⁻¹ • covarianceTileCenter L j = covarianceTileCenter (R⁻¹ * L) j := by
    intro j
    funext i
    simp only [covarianceTileCenter, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hw : ∀ a : JointObservationIndex d,
      Summable (fun j : Fin d → ℤ => ‖F (R⁻¹ • covarianceTileCenter L j) a‖) := by
    intro a
    have hs := summable_schwartz_lattice_norm (mul_pos (inv_pos.mpr hR) hLpos) hN F
    simp_rw [hgrid]
    exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => PiLp.norm_apply_le (F (covarianceTileCenter (R⁻¹ * L) j)) a) hs
  obtain ⟨hae, hmem⟩ := weighted_series_memLp hX c hc hb
    (fun j a => F (R⁻¹ • covarianceTileCenter L j) a) hw
  exact ⟨hae, hmem.const_mul _⟩

/-- Independence and genuine series membership at the exact dyadic mesh of
the test-block contract, with all thresholds chosen before the law. -/
theorem covarianceTestBlocks_dyadic_series
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : 2 * d ≤ N) (θ : ℝ) (hθ : 0 < θ) :
    ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ R : ℝ, R₀ ≤ R →
        let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
        let X := fun j : Fin d → ℤ =>
          covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
            (covarianceTileCenter L j) (fun _ => 1)
        iIndepFun X (reducedLaw Q) ∧
        ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
          (∀ᵐ ω ∂reducedLaw Q, Summable (fun j =>
            ∑ a, F (R⁻¹ • covarianceTileCenter L j) a * (X j ω a : ℂ))) ∧
          MemLp (covarianceTestBlocks d hd D s δ γ η β h Q R L F) 2 (reducedLaw Q) ∧
          MemLp (covarianceTestBlocks d hd D s δ γ η β h Q R L G) 2 (reducedLaw Q) := by
  obtain ⟨Li, _, hind⟩ := covarianceTestBlocks_children_independent hjl d hd D s δ γ η β h
  obtain ⟨Ls, _, hmem⟩ := covarianceTestBlocks_summable_memLp hclt hjl d hd D s δ γ η β h N hN
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hθ).eventually_ge_atTop (2 * max Li Ls))
  refine ⟨max R₁ 2, le_max_right _ _, ?_⟩
  intro Q hQ R hR
  have hR2 : 2 ≤ R := (le_max_right R₁ 2).trans hR
  have hp := hR₁ R ((le_max_left _ _).trans hR)
  have hb := dyadic_scale_bounds (by linarith : 1 ≤ R) hθ rfl
  have hL : max Li Ls ≤ (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2) := by
    linarith [hb.2.2]
  refine ⟨hind Q hQ _ ((le_max_left _ _).trans hL), ?_⟩
  intro F G
  have hF := hmem Q hQ _ ((le_max_right _ _).trans hL) R (by linarith) F
  have hG := hmem Q hQ _ ((le_max_right _ _).trans hL) R (by linarith) G
  exact ⟨hF.1, hF.2, hG.2⟩


/-- The actual normalized test-block series has a uniform L² bound with a
structural constant chosen before the law and both mesh parameters. -/
theorem covarianceTestBlocks_uniform_l2
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : 2 * d ≤ N) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ L : ℝ, L₀ ≤ L → ∀ R : ℝ, L ≤ R →
        ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        covarianceComplexL2Size (reducedLaw Q)
          (covarianceTestBlocks d hd D s δ γ η β h Q R L F) ≤
            C * schwartzTestNorm N F := by
  have hwin := h
  obtain ⟨_, _, _, _, _, _, _, _, hηlower, _, _⟩ := hwin
  have hη : 0 < η := by linarith
  obtain ⟨B, Lc, hB, hLc, hdata⟩ :=
    covarianceTestBlocks_children_l2 hclt hjl d hd D s δ γ η β h
  obtain ⟨Li, _, hind⟩ :=
    covarianceTestBlocks_children_independent hjl d hd D s δ γ η β h
  obtain ⟨Lm, hLm⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually_ge_atTop (2 * D.dependenceRange))
  let A : ℝ := (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * B ^ 2 * 3 ^ d
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
  refine ⟨A + 1, max Lc (max Li Lm), by positivity,
    hLc.trans (le_max_left _ _), ?_⟩
  intro Q hQ L hL R hLR F
  haveI := reducedLaw_probability Q
  let X := fun j : Fin d → ℤ =>
    covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
      (covarianceTileCenter L j) (fun _ => 1)
  have hLcL := (le_max_left Lc (max Li Lm)).trans hL
  have hLiL := (le_max_left Li Lm).trans ((le_max_right Lc _).trans hL)
  have hLmL := (le_max_right Li Lm).trans ((le_max_right Lc _).trans hL)
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < Lc) hLcL
  have hR : 0 < R := hLpos.trans_le hLR
  have hr := hLm L hLmL
  have hX : ∀ j, L2Vec (reducedLaw Q) (X j) := fun j => (hdata Q hQ L hLcL j).1
  let c := fun a => eLpNorm (fun ω => X 0 ω a) 2 (reducedLaw Q)
  have hc : ∀ a, c a ≠ ⊤ := fun a => ((hX 0).coord_memLp a).ne
  have hb : ∀ j a, eLpNorm (fun ω => X j ω a) 2 (reducedLaw Q) ≤ c a := by
    intro j a
    have hid := covarianceTestBlocks_child_identDistrib hjl d hd D s δ γ η β h
      Q hQ L hr j
    have he := (hid.comp (measurable_pi_apply a)).eLpNorm_eq 2
    have hz : covarianceTileCenter L (0 : Fin d → ℤ) = 0 := by
      funext i
      simp only [covarianceTileCenter, Pi.zero_apply, Int.cast_zero, mul_zero]
    dsimp only [c, X]
    rw [hz]
    exact he.le
  have hi : iIndepFun X (reducedLaw Q) := hind Q hQ L hLiL
  have hm : ∀ j a, (∫ ω, X j ω a ∂reducedLaw Q) = 0 := fun j a =>
    (covarianceTestBlocks_child_integrable_mean hjl d hd D s δ γ η β h
      Q hQ L hr j a).2
  have hs := testBlocks_mesh_l2Size_sq_le hX c hc hb hi hm hB.le
    (fun j => (hdata Q hQ L hLcL j).2) hR hLpos hLR hN F
  have hsq : covarianceComplexL2Size (reducedLaw Q)
      (covarianceTestBlocks d hd D s δ γ η β h Q R L F) ^ 2 ≤
        A * schwartzTestNorm N F ^ 2 := by
    change l2Size (reducedLaw Q)
      (fun ω => (((L / R) ^ ((d : ℝ) / 2) : ℝ) : ℂ) *
        ∑' j : Fin d → ℤ, ∑ a,
          F (R⁻¹ • covarianceTileCenter L j) a * (X j ω a : ℂ)) ^ 2 ≤ _
    rw [l2Size_mesh_normalization_sq _ _ (div_pos hLpos hR).le]
    exact hs
  have hw : (1 + euclideanNorm (0 : Vec d)) ^ N * ‖F 0‖ ≤
      schwartzTestNorm N F := by
    apply le_csSup (schwartzTestNorm_set_bddAbove N F)
    exact ⟨⟨0, by omega⟩, Fin.elim0, 0, by simp only [iteratedFDeriv_zero_apply]⟩
  have hF : 0 ≤ schwartzTestNorm N F :=
    (mul_nonneg (pow_nonneg (by unfold euclideanNorm; positivity) N) (norm_nonneg _)).trans hw
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hF)).1
  calc
    _ ≤ A * schwartzTestNorm N F ^ 2 := hsq
    _ ≤ (A + 1) ^ 2 * schwartzTestNorm N F ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg A]) (sq_nonneg _)
    _ = _ := by ring


/-- Exact bilinear covariance of the actual normalized infinite block series.
Stationarity identifies every diagonal block matrix with the origin matrix;
all joint cross-coordinates are retained. -/
theorem covarianceTestBlocks_bilinear_diagonal
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : 2 * d ≤ N) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ L : ℝ, L₀ ≤ L → ∀ R : ℝ, 0 < R →
        ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        let B := covarianceBlockMatrix (reducedLaw Q)
          (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β) 0 (fun _ => 1))
        (∫ ω, covarianceTestBlocks d hd D s δ γ η β h Q R L F ω *
          covarianceTestBlocks d hd D s δ γ η β h Q R L G ω ∂reducedLaw Q) =
          (((L / R) ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ,
            ∑ a, ∑ b, F (R⁻¹ • covarianceTileCenter L j) a * (B a b : ℂ) *
              G (R⁻¹ • covarianceTileCenter L j) b := by
  have hwin := h
  obtain ⟨_, _, _, _, _, _, _, _, hηlower, _, _⟩ := hwin
  have hη : 0 < η := by linarith
  obtain ⟨_, Lc, _, hLc, hdata⟩ :=
    covarianceTestBlocks_children_l2 hclt hjl d hd D s δ γ η β h
  obtain ⟨Li, _, hind⟩ :=
    covarianceTestBlocks_children_independent hjl d hd D s δ γ η β h
  obtain ⟨Lm, hLm⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually_ge_atTop (2 * D.dependenceRange))
  refine ⟨max Lc (max Li Lm), hLc.trans (le_max_left _ _), ?_⟩
  intro Q hQ L hL R hR F G
  haveI := reducedLaw_probability Q
  let X := fun j : Fin d → ℤ =>
    covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
      (covarianceTileCenter L j) (fun _ => 1)
  have hLcL := (le_max_left Lc (max Li Lm)).trans hL
  have hLiL := (le_max_left Li Lm).trans ((le_max_right Lc _).trans hL)
  have hLmL := (le_max_right Li Lm).trans ((le_max_right Lc _).trans hL)
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < Lc) hLcL
  have hr := hLm L hLmL
  have hX : ∀ j, L2Vec (reducedLaw Q) (X j) := fun j => (hdata Q hQ L hLcL j).1
  let c := fun a => eLpNorm (fun ω => X 0 ω a) 2 (reducedLaw Q)
  have hc : ∀ a, c a ≠ ⊤ := fun a => ((hX 0).coord_memLp a).ne
  have hb : ∀ j a, eLpNorm (fun ω => X j ω a) 2 (reducedLaw Q) ≤ c a := by
    intro j a
    have hid := covarianceTestBlocks_child_identDistrib hjl d hd D s δ γ η β h
      Q hQ L hr j
    have he := (hid.comp (measurable_pi_apply a)).eLpNorm_eq 2
    have hz : covarianceTileCenter L (0 : Fin d → ℤ) = 0 := by
      funext i
      simp only [covarianceTileCenter, Pi.zero_apply, Int.cast_zero, mul_zero]
    dsimp only [c, X]
    rw [hz]
    exact he.le
  have hm : ∀ j a, (∫ ω, X j ω a ∂reducedLaw Q) = 0 := fun j a =>
    (covarianceTestBlocks_child_integrable_mean hjl d hd D s δ γ η β h
      Q hQ L hr j a).2
  have hx (j : Fin d → ℤ) :
      R⁻¹ • covarianceTileCenter L j = covarianceTileCenter (L / R) j := by
    funext i
    simp only [covarianceTileCenter, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have hw (H : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (a : JointObservationIndex d) :
      Summable (fun j : Fin d → ℤ => ‖H (R⁻¹ • covarianceTileCenter L j) a‖) := by
    simp_rw [hx]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => PiLp.norm_apply_le (H (covarianceTileCenter (L / R) j)) a)
      (summable_schwartz_lattice_norm (div_pos hLpos hR) hN H)
  have hcov := weighted_series_bilinear_covariance hX c hc hb
    (fun j a => F (R⁻¹ • covarianceTileCenter L j) a)
    (fun j a => G (R⁻¹ • covarianceTileCenter L j) a)
    (hw F) (hw G) (hind Q hQ L hLiL) hm
  have hmat (j : Fin d → ℤ) (a b : JointObservationIndex d) :
      covMat (reducedLaw Q) (X j) a b = covarianceBlockMatrix (reducedLaw Q)
        (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β) 0 (fun _ => 1)) a b := by
    have hid := covarianceTestBlocks_child_identDistrib hjl d hd D s δ γ η β h
      Q hQ L hr j
    exact (hid.comp (show Measurable (fun v : JointObservationIndex d → ℝ => v a * v b)
      from by fun_prop)).integral_eq
  let cL : ℂ := (((L / R) ^ ((d : ℝ) / 2) : ℝ) : ℂ)
  have hreal : ((L / R) ^ ((d : ℝ) / 2)) ^ 2 = (L / R) ^ d := by
    calc
      _ = (L / R) ^ (((d : ℝ) / 2) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast (div_pos hLpos hR).le ((d : ℝ) / 2) 2).symm
      _ = (L / R) ^ (d : ℝ) := by congr 1; ring
      _ = (L / R) ^ d := Real.rpow_natCast _ _
  have hpow : cL ^ 2 = (((L / R) ^ d : ℝ) : ℂ) := by
    dsimp only [cL]
    exact_mod_cast hreal
  change (∫ ω, (cL * ∑' j, ∑ a,
    F (R⁻¹ • covarianceTileCenter L j) a * (X j ω a : ℂ)) *
    (cL * ∑' j, ∑ a, G (R⁻¹ • covarianceTileCenter L j) a * (X j ω a : ℂ))
    ∂reducedLaw Q) = _
  calc
    _ = cL ^ 2 * ∫ ω, (∑' j, ∑ a,
        F (R⁻¹ • covarianceTileCenter L j) a * (X j ω a : ℂ)) *
        (∑' j, ∑ a, G (R⁻¹ • covarianceTileCenter L j) a * (X j ω a : ℂ))
        ∂reducedLaw Q := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by ring)
    _ = _ := by
      rw [hpow, hcov]
      congr 1
      apply tsum_congr
      intro j
      simp_rw [hmat j]

/-- At every sufficiently large natural dyadic block scale, the stochastic
covariance can be replaced by the canonical matrix inside the lattice sum. -/
theorem covarianceTestBlocks_canonical_lattice_rate
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (hrate : node_e_u3A_block_u2D_cov_u2D_rateStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : 2 * d ≤ N) :
    ∃ C L₀ κ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧ 0 < κ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ n : ℕ, L₀ ≤ (2 : ℝ) ^ n →
        ∀ R : ℝ, (2 : ℝ) ^ n ≤ R →
        ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        let L := (2 : ℝ) ^ n
        let A := covarianceDyadicLimit d hd D s δ γ η β h Q
        ‖(∫ ω, covarianceTestBlocks d hd D s δ γ η β h Q R L F ω *
          covarianceTestBlocks d hd D s δ γ η β h Q R L G ω ∂reducedLaw Q) -
          (((L / R) ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ a, ∑ b,
            F (R⁻¹ • covarianceTileCenter L j) a * (A a b : ℂ) *
              G (R⁻¹ • covarianceTileCenter L j) b‖ ≤
          C * schwartzTestNorm N F * schwartzTestNorm N G * L ^ (-κ) := by
  obtain ⟨Ld, hLd, hdiag⟩ :=
    covarianceTestBlocks_bilinear_diagonal hclt hjl d hd D s δ γ η β h N hN
  obtain ⟨B, Lr, κ, hB, _, hκ, hrate⟩ := hrate d hd D s δ γ η β h
  let K : ℝ := (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 * 3 ^ d
  have hK : 0 < K := by
    haveI : Nonempty (JointObservationIndex d) := ⟨Sum.inr ()⟩
    dsimp only [K]
    positivity
  refine ⟨K * B, max Ld Lr, κ, mul_pos hK hB,
    hLd.trans (le_max_left _ _), hκ, ?_⟩
  intro Q hQ n hn R hLR F G
  have hLpos : 0 < (2 : ℝ) ^ n := by positivity
  have hR : 0 < R := hLpos.trans_le hLR
  have hdg := hdiag Q hQ _ ((le_max_left _ _).trans hn) R hR F G
  dsimp only at hdg ⊢
  rw [hdg]
  have herr := (hrate Q hQ).2.2.2 n ((le_max_right _ _).trans hn)
  have hm : covarianceMatrixSize
      (covarianceBlockMatrix (reducedLaw Q)
        (covarianceBlock d hd D s δ γ η β h Q (((2 : ℝ) ^ n) ^ η)
          ((2 : ℝ) ^ n) ((2 : ℝ) ^ n - ((2 : ℝ) ^ n) ^ β) 0 (fun _ => 1)) -
        covarianceDyadicLimit d hd D s δ γ η β h Q) ≤ B * ((2 : ℝ) ^ n) ^ (-κ) := by
    exact (le_add_of_nonneg_left (by unfold covarianceMatrixSize; positivity)).trans herr
  have he := testBlocks_mesh_matrix_sub_le hR hLpos hLR (by omega : d ≤ N)
    (covarianceBlockMatrix (reducedLaw Q)
      (covarianceBlock d hd D s δ γ η β h Q (((2 : ℝ) ^ n) ^ η)
        ((2 : ℝ) ^ n) ((2 : ℝ) ^ n - ((2 : ℝ) ^ n) ^ β) 0 (fun _ => 1)))
    (covarianceDyadicLimit d hd D s δ γ η β h Q) F G
  apply he.trans
  have hfg := mul_nonneg (schwartz_norm_nonneg N F) (schwartz_norm_nonneg N G)
  have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hK.le) hfg
  convert ht using 1 <;> (try dsimp only [K]) <;> ring

/-- The canonical-matrix lattice comparison at the exact floor-defined mesh
of the test-block contract, for every positive theta below one. -/
theorem covarianceTestBlocks_canonical_dyadic_rate
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (hrate : node_e_u3A_block_u2D_cov_u2D_rateStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : 2 * d ≤ N) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C R₀ κ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧ 0 < κ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ R : ℝ, R₀ ≤ R →
        ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
        let A := covarianceDyadicLimit d hd D s δ γ η β h Q
        ‖(∫ ω, covarianceTestBlocks d hd D s δ γ η β h Q R L F ω *
          covarianceTestBlocks d hd D s δ γ η β h Q R L G ω ∂reducedLaw Q) -
          (((L / R) ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ a, ∑ b,
            F (R⁻¹ • covarianceTileCenter L j) a * (A a b : ℂ) *
              G (R⁻¹ • covarianceTileCenter L j) b‖ ≤
          C * schwartzTestNorm N F * schwartzTestNorm N G * L ^ (-κ) := by
  obtain ⟨C, L₀, κ, hC, _, hκ, hrate⟩ :=
    covarianceTestBlocks_canonical_lattice_rate hclt hjl hrate d hd D s δ γ η β h N hN
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hθ).eventually_ge_atTop (2 * L₀))
  refine ⟨C, max R₁ 2, κ, hC, le_max_right _ _, hκ, ?_⟩
  intro Q hQ R hR F G
  have hR1 : 1 ≤ R := by linarith [(le_max_right R₁ 2).trans hR]
  have hp := hR₁ R ((le_max_left _ _).trans hR)
  let m := Int.floor (Real.log (R ^ θ) / Real.log 2)
  have hm : 0 ≤ m := Int.floor_nonneg.mpr
    (div_nonneg (Real.log_nonneg (Real.one_le_rpow hR1 hθ.le))
      (Real.log_pos one_lt_two).le)
  have hpow : (2 : ℝ) ^ m.toNat = (2 : ℝ) ^ m := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hm]
  have hb := dyadic_scale_bounds hR1 hθ rfl
  have hL : L₀ ≤ (2 : ℝ) ^ m.toNat := by
    rw [hpow]
    dsimp only [m]
    linarith [hb.2.2]
  have hLR : (2 : ℝ) ^ m.toNat ≤ R := by
    rw [hpow]
    exact hb.2.1.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hR1 hθ1.le)
  have he := hrate Q hQ m.toNat hL R hLR F G
  simpa only [hpow, m] using he


/-- The complete covariance estimate against the spatial integral, at the
exact floor-defined mesh, with constants preceding the environment law. -/
theorem covarianceTestBlocks_spatial_covariance_rate
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (hrate : node_e_u3A_block_u2D_cov_u2D_rateStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : 2 * d ≤ N) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C R₀ κ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧ 0 < κ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ R : ℝ, R₀ ≤ R →
        ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
        let A := covarianceDyadicLimit d hd D s δ γ η β h Q
        ‖(∫ ω, covarianceTestBlocks d hd D s δ γ η β h Q R L F ω *
          covarianceTestBlocks d hd D s δ γ η β h Q R L G ω ∂reducedLaw Q) -
          ∫ x : Vec d, ∑ a, ∑ b, F x a * (A a b : ℂ) * G x b‖ ≤
          C * schwartzTestNorm N F * schwartzTestNorm N G * (L ^ (-κ) + L / R) := by
  obtain ⟨C, R₀, κ, hC, hR₀, hκ, hcov⟩ :=
    covarianceTestBlocks_canonical_dyadic_rate hclt hjl hrate d hd D s δ γ η β h N hN θ hθ hθ1
  obtain ⟨B, _, _, hB, _, _, hmat⟩ := hrate d hd D s δ γ η β h
  let K := (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 *
    (d : ℝ) * (2 + (d : ℝ)) ^ (2 * N) * 3 ^ d * B
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨C + K, R₀, κ, add_pos_of_pos_of_nonneg hC hK, hR₀, hκ, ?_⟩
  intro Q hQ R hR F G
  let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
  let A := covarianceDyadicLimit d hd D s δ γ η β h Q
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hLpos : 0 < L := by dsimp only [L]; positivity
  have hb := dyadic_scale_bounds hR1 hθ rfl
  have hLR : L ≤ R := hb.2.1.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR1 hθ1.le)
  have hm : covarianceMatrixSize A ≤ B := (hmat Q hQ).2.1
  have he := testBlocks_mesh_riemann_error_le (by omega : 1 ≤ N) (by omega : d ≤ N)
    hRpos hLpos hLR A F G
  have hfg : 0 ≤ schwartzTestNorm N F * schwartzTestNorm N G :=
    mul_nonneg (schwartz_norm_nonneg N F) (schwartz_norm_nonneg N G)
  have hr : ‖(((L / R) ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ a, ∑ b,
        F (R⁻¹ • covarianceTileCenter L j) a * (A a b : ℂ) *
          G (R⁻¹ • covarianceTileCenter L j) b -
        (∫ x, ∑ a, ∑ b, F x a * (A a b : ℂ) * G x b)‖ ≤
      K * schwartzTestNorm N F * schwartzTestNorm N G * (L / R) := by
    apply he.trans
    have hh := mul_le_mul_of_nonneg_left hm
      (by positivity : 0 ≤ (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 *
        (d : ℝ) * (2 + (d : ℝ)) ^ (2 * N) * 3 ^ d)
    have ht := mul_le_mul_of_nonneg_right hh
      (mul_nonneg hfg (div_nonneg hLpos.le hRpos.le))
    convert ht using 1 <;> (try dsimp only [K]) <;> ring
  have hc := hcov Q hQ R hR F G
  dsimp only at hc ⊢
  change ‖_ - _‖ ≤ (C + K) * schwartzTestNorm N F * schwartzTestNorm N G *
    (L ^ (-κ) + L / R)
  have ht := dist_triangle
    (∫ ω, covarianceTestBlocks d hd D s δ γ η β h Q R L F ω *
      covarianceTestBlocks d hd D s δ γ η β h Q R L G ω ∂reducedLaw Q)
    ((((L / R) ^ d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ a, ∑ b,
      F (R⁻¹ • covarianceTileCenter L j) a * (A a b : ℂ) *
        G (R⁻¹ • covarianceTileCenter L j) b)
    (∫ x : Vec d, ∑ a, ∑ b, F x a * (A a b : ℂ) * G x b)
  simp only [dist_eq_norm] at ht
  apply (ht.trans (add_le_add hc hr)).trans
  have h1 : C ≤ C + K := le_add_of_nonneg_right hK
  have h2 : K ≤ C + K := le_add_of_nonneg_left hC.le
  have hf1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hfg)
    (Real.rpow_nonneg hLpos.le (-κ))
  have hf2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hfg)
    (div_nonneg hLpos.le hRpos.le)
  convert add_le_add hf1 hf2 using 1 <;> ring

end EinsteinFull.Blueprint
