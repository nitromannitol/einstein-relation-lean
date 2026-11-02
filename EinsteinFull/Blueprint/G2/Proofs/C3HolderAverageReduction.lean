import EinsteinFull.Calculus.C3HolderForwardClock
import EinsteinFull.Calculus.C5HolderTranspose
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

private lemma holder_bound_mono {α α' C C' Cp Cp' b w z t N : ℝ}
    (hα : α ≤ α') (hC : C' ≤ C) (hC' : 0 ≤ C') (hCp : Cp' ≤ Cp)
    (hb : 0 < b) (hb1 : b ≤ 1) (hw : 1 ≤ w)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hN : 0 ≤ N) :
    C' * b ^ (α' / 2) * w ^ C' * Real.exp (Cp' * z * t) * N ≤
      C * b ^ (α / 2) * w ^ C * Real.exp (Cp * z * t) * N := by
  have hC0 : 0 ≤ C := hC'.trans hC
  have hw0 : 0 ≤ w := (by norm_num : (0 : ℝ) ≤ 1).trans hw
  have hbpow := Real.rpow_le_rpow_of_exponent_ge hb hb1 (div_le_div_of_nonneg_right hα (by norm_num : (0 : ℝ) ≤ 2))
  have hwpow := Real.rpow_le_rpow_of_exponent_le hw hC
  have hexp := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCp hz) ht)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul (mul_le_mul hC hbpow (Real.rpow_nonneg hb.le _) hC0)
      hwpow (Real.rpow_nonneg (by linarith only [hw]) _) (by positivity))
      hexp (Real.exp_nonneg _) (by positivity)) hN

/-- Gaussian unsmoothing for all actual endpoints, with common structural constants. -/
theorem node_e_u3A_holder_u2D_average_of_deps
    (h0 : node_e_u3A_local_u2D_timeStmt)
    (h1 : node_e_u3A_lp_u2D_growthStmt)
    (h2 : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (h3 : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt) :
    node_e_u3A_holder_u2D_averageStmt := by
  intro d hd D
  obtain ⟨αf, hαf, hf⟩ := holder_average_forward_clock_of_deps h0 h1 h2 h3 d hd D
  obtain ⟨αt, hαt, ht⟩ := holder_average_transpose_of_deps h0 h1 h2 h3 d hd D
  refine ⟨min αf αt, lt_min hαf hαt, ?_⟩
  intro p hp
  obtain ⟨Cf, Cpf, hCf, hCpf, hf⟩ := hf p hp
  obtain ⟨Ct, Cpt, hCt, hCpt, ht⟩ := ht p hp
  refine ⟨max Cf Ct, max Cpf Cpt, hCf.trans (le_max_left _ _),
    hCpf.trans_le (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P T hP hT ν t htpos U U8
  have hw : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) :=
    le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  by_cases hν : ν = .inr true
  · subst ν
    obtain ⟨hm, hb⟩ := ht Q hQ β a μ hβ ha hμ ζ P T hP hT t htpos
    refine ⟨hm, ?_⟩
    intro b hbpos hbsmall hbt
    obtain ⟨hm, hbound⟩ := hb b hbpos hbsmall hbt
    refine ⟨hm, hbound.trans ?_⟩
    exact holder_bound_mono (min_le_right _ _) (le_max_right _ _) (by linarith only [hCt])
      (le_max_right _ _) hbpos (by linarith only [hbsmall]) hw
      (sq_nonneg _) t.coe_nonneg ENNReal.toReal_nonneg
  · obtain ⟨hm, hb⟩ := hf Q hQ β a μ hβ ha hμ ζ P T hP hT ν hν t htpos
    refine ⟨hm, ?_⟩
    intro b hbpos hbsmall hbt
    obtain ⟨hm, hbound⟩ := hb b hbpos hbsmall hbt
    refine ⟨hm, hbound.trans ?_⟩
    exact holder_bound_mono (min_le_left _ _) (le_max_left _ _) (by linarith only [hCf])
      (le_max_left _ _) hbpos (by linarith only [hbsmall]) hw
      (sq_nonneg _) t.coe_nonneg ENNReal.toReal_nonneg
end EinsteinFull.Blueprint
