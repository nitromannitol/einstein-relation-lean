import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_cov_u2D_rate
import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_recursion
import EinsteinFull.Calculus.C10BlockSupport
import EinsteinFull.Blueprint.G3.Proofs.S1BlockRecursion

/-! Dyadic covariance convergence and rates from the recursion and the
reviewed joint-localization dependency. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinFull.Calculus.C10

/-- The genuine full-block dyadic covariance converges to the selected limit.
This part of the covariance-rate contract uses only its recorded dependency. -/
theorem covarianceDyadicLimit_entry_tendsto_of_recursion
    (hrec : node_e_u3A_block_u2D_recursionStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (a b : JointObservationIndex d) :
    Tendsto (fun n : ℕ => covarianceBlockMatrix (reducedLaw Q)
      (covarianceBlock d hd D s δ γ η β h Q (((2 : ℝ) ^ n) ^ η)
        ((2 : ℝ) ^ n) ((2 : ℝ) ^ n) 0 (fun _ => 1)) a b)
      atTop (nhds (covarianceDyadicLimit d hd D s δ γ η β h Q a b)) := by
  obtain ⟨C, L₀, κ, -, -, hκ, -, hrecQ⟩ := hrec d hd D s δ γ η β h
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop L₀)
  apply tendsto_limUnder_of_geometric_increments _ C ((2 : ℝ) ^ (-κ))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hκ)) N
  intro n hn
  have hb := (hrecQ Q hQ ((2 : ℝ) ^ n) (hN n hn)).2.2.2.2.2.2.2.2.2
  have he := abs_entry_le_frob
    (covarianceBlockMatrix (reducedLaw Q)
      (covarianceBlock d hd D s δ γ η β h Q ((2 * (2 : ℝ) ^ n) ^ η)
        (2 * (2 : ℝ) ^ n) (2 * (2 : ℝ) ^ n) 0 (fun _ => 1)) -
      covarianceBlockMatrix (reducedLaw Q)
        (covarianceBlock d hd D s δ γ η β h Q (((2 : ℝ) ^ n) ^ η)
          ((2 : ℝ) ^ n) ((2 : ℝ) ^ n) 0 (fun _ => 1))) a b
  have hp : ((2 : ℝ) ^ n) ^ (-κ) = ((2 : ℝ) ^ (-κ)) ^ n := by
    rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  simpa only [Matrix.sub_apply, pow_succ, mul_comm, hp] using he.trans hb

/-- Exact covariance-rate reduction with the reviewed, ordered dependencies. -/
theorem node_e_u3A_block_u2D_cov_u2D_rate_of_deps
    (hrec : node_e_u3A_block_u2D_recursionStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt) :
    node_e_u3A_block_u2D_cov_u2D_rateStmt := by
  intro d hd D s δ γ η β h
  obtain ⟨C, Lr, κ, hC, hLr, hκ, hκβ, hrecQ⟩ := hrec d hd D s δ γ η β h
  have hη : 0 < η := by
    obtain ⟨_, _, _, _, _, _, _, _, hh, _, _⟩ := h
    linarith
  obtain ⟨Lm, hLm⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually_ge_atTop (2 * D.dependenceRange))
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop
      (max Lr (max Lm 2)))
  have hlarge (n : ℕ) (hn : N ≤ n) : Lr ≤ (2 : ℝ) ^ n ∧ Lm ≤ (2 : ℝ) ^ n ∧
      2 ≤ (2 : ℝ) ^ n := by
    have hh := hN n hn
    exact ⟨(le_max_left _ _).trans hh,
      (le_max_left Lm 2).trans ((le_max_right _ _).trans hh),
      (le_max_right Lm 2).trans ((le_max_right _ _).trans hh)⟩
  let r : ℝ := (2 : ℝ) ^ (-κ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hr : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hκ)
  let B : ℝ := (Fintype.card (JointObservationIndex d) : ℝ) * (C / (1 - r))
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (div_nonneg hC.le (by linarith))
  refine ⟨C ^ 2 + 2 * B + 3 * C ^ 2 + 1, (2 : ℝ) ^ N, κ,
    by nlinarith [sq_nonneg C], (hlarge N le_rfl).2.2, hκ, ?_⟩
  intro Q hQ
  haveI := reducedLaw_probability Q
  let X := fun n : ℕ => covarianceBlock d hd D s δ γ η β h Q
    (((2 : ℝ) ^ n) ^ η) ((2 : ℝ) ^ n) ((2 : ℝ) ^ n) 0 (fun _ => 1)
  let Xm := fun n : ℕ => covarianceBlock d hd D s δ γ η β h Q
    (((2 : ℝ) ^ n) ^ η) ((2 : ℝ) ^ n) ((2 : ℝ) ^ n - ((2 : ℝ) ^ n) ^ β) 0 (fun _ => 1)
  let V := fun n : ℕ => covarianceBlockMatrix (reducedLaw Q) (X n)
  let A := covarianceDyadicLimit d hd D s δ γ η β h Q
  have hdata (n : ℕ) (hn : N ≤ n) := hrecQ Q hQ ((2 : ℝ) ^ n) (hlarge n hn).1
  have hL2 (n : ℕ) (hn : N ≤ n) :
      EinsteinFull.Calculus.S1.L2Vec (reducedLaw Q) (X n) ∧
      EinsteinFull.Calculus.S1.L2Vec (reducedLaw Q) (Xm n) := by
    have hs := cov_lsf hjl d hd D s δ γ η β h Q hQ (((2 : ℝ) ^ n) ^ η)
      (hLm _ (hlarge n hn).2.1)
    exact ⟨EinsteinFull.Calculus.S1.L2Vec_blk_one hs (reducedLaw_hT Q) _
      (EinsteinFull.Calculus.S1.volume_clockBlockCube_lt_top _ _) (hdata n hn).1,
      EinsteinFull.Calculus.S1.L2Vec_blk_one hs (reducedLaw_hT Q) _
        (EinsteinFull.Calculus.S1.volume_clockBlockCube_lt_top _ _) (hdata n hn).2.1⟩
  have ht (a b) : Tendsto (fun n => V n a b) atTop (nhds (A a b)) :=
    covarianceDyadicLimit_entry_tendsto_of_recursion hrec d hd D s δ γ η β h Q hQ a b
  have hinc (a b) (n : ℕ) (hn : N ≤ n) :
      |V (n + 1) a b - V n a b| ≤ C * r ^ n := by
    have hb := (hdata n hn).2.2.2.2.2.2.2.2.2
    have he := abs_entry_le_frob
      (covarianceBlockMatrix (reducedLaw Q)
        (covarianceBlock d hd D s δ γ η β h Q ((2 * (2 : ℝ) ^ n) ^ η)
          (2 * (2 : ℝ) ^ n) (2 * (2 : ℝ) ^ n) 0 (fun _ => 1)) - V n) a b
    have hp : ((2 : ℝ) ^ n) ^ (-κ) = r ^ n := by
      dsimp [r]
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
        Real.rpow_natCast]
    exact (show |V (n + 1) a b - V n a b| ≤ C * r ^ n by
      simpa only [V, X, Matrix.sub_apply, pow_succ, mul_comm, hp] using he.trans hb)
  have hfull (n : ℕ) (hn : N ≤ n) :
      covarianceMatrixSize (V n - A) ≤ B * ((2 : ℝ) ^ n) ^ (-κ) := by
    have hp : ((2 : ℝ) ^ n) ^ (-κ) = r ^ n := by
      dsimp [r]
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
        Real.rpow_natCast]
    have hb := frob_le_of_entry_abs (V n - A)
      (div_nonneg (mul_nonneg hC.le (pow_nonneg hr0 n))
        (by linarith : 0 ≤ 1 - r)) (fun a b =>
          abs_sub_limUnder_le_of_geometric_increments (fun n => V n a b) C r hr N
            (hinc a b) n hn)
    calc
      _ ≤ (Fintype.card (JointObservationIndex d) : ℝ) * (C * r ^ n / (1 - r)) := hb
      _ = B * ((2 : ℝ) ^ n) ^ (-κ) := by rw [hp]; dsimp [B]; ring
  have hpsd : A.PosSemidef := posSemidef_of_entrywise_tendsto ht
    (eventually_atTop.2 ⟨N, fun n hn => covMat_posSemidef (hL2 n hn).1⟩)
  have hbound : covarianceMatrixSize A ≤ C ^ 2 := by
    apply le_of_tendsto (tendsto_frob ht)
    apply eventually_atTop.2
    refine ⟨N, fun n hn => ?_⟩
    have hb := EinsteinFull.Calculus.S1.frob_cross_le (hL2 n hn).1 (hL2 n hn).1
    have hx : EinsteinFull.Calculus.S1.vl2 (reducedLaw Q) (X n) ≤ C := (hdata n hn).2.2.1
    exact hb.trans (by nlinarith [EinsteinFull.Calculus.S1.vl2_nonneg (reducedLaw Q) (X n)])
  refine ⟨hpsd, by nlinarith [sq_nonneg C], ht, ?_⟩
  intro n hn
  have hnN : N ≤ n := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hn
  obtain ⟨hX, hXm⟩ := hL2 n hnN
  have hx : EinsteinFull.Calculus.S1.vl2 (reducedLaw Q) (X n) ≤ C := (hdata n hnN).2.2.1
  have hL : 1 ≤ (2 : ℝ) ^ n := by linarith [(hlarge n hnN).2.2]
  let t : ℝ := ((2 : ℝ) ^ n) ^ (-κ)
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hdif : EinsteinFull.Calculus.S1.vl2 (reducedLaw Q) (fun ω => X n ω - Xm n ω) ≤ C * t := by
    exact (hdata n hnN).2.2.2.1 |>.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hC.le)
  have hxm : EinsteinFull.Calculus.S1.vl2 (reducedLaw Q) (Xm n) ≤ 2 * C := by
    have hh := vl2_le_add_sub hXm hX
    rw [vl2_sub_comm] at hh
    nlinarith [mul_le_of_le_one_right hC.le ht1]
  have htrim : covarianceMatrixSize
      (covarianceBlockMatrix (reducedLaw Q) (Xm n) - V n) ≤ 3 * C ^ 2 * t := by
    have hh := EinsteinFull.Calculus.S1.frob_covMat_sub_le hXm hX
    rw [vl2_sub_comm] at hh
    have hh' := mul_le_mul hdif (add_le_add hxm hx)
      (add_nonneg (EinsteinFull.Calculus.S1.vl2_nonneg _ _) (EinsteinFull.Calculus.S1.vl2_nonneg _ _))
      (mul_nonneg hC.le ht0)
    exact hh.trans (hh'.trans_eq (by ring))
  have htri := EinsteinFull.Calculus.S1.frob_add_le
    (covarianceBlockMatrix (reducedLaw Q) (Xm n) - V n) (V n - A)
  have he : (covarianceBlockMatrix (reducedLaw Q) (Xm n) - V n) + (V n - A) =
      covarianceBlockMatrix (reducedLaw Q) (Xm n) - A := by abel
  rw [he] at htri
  change covarianceMatrixSize (covarianceBlockMatrix (reducedLaw Q) (Xm n) - A) ≤
    covarianceMatrixSize (covarianceBlockMatrix (reducedLaw Q) (Xm n) - V n) +
      covarianceMatrixSize (V n - A) at htri
  have hf : covarianceMatrixSize (V n - A) ≤ B * t := hfull n hnN
  change covarianceMatrixSize (V n - A) +
    covarianceMatrixSize (covarianceBlockMatrix (reducedLaw Q) (Xm n) - A) ≤
      (C ^ 2 + 2 * B + 3 * C ^ 2 + 1) * t
  nlinarith only [hf, htrim, htri, mul_nonneg (sq_nonneg C) ht0, ht0]

end EinsteinFull.Blueprint
