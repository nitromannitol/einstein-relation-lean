import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer
import EinsteinFull.Work.W5.StructuralRegenerationMomentsProof

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- At a common admissible construction scale, combine the GMP no-return
bound with the transferred tail and integrate the actual first-cycle law.
This proves `app:regen-tails` (`paper/main.tex:1455–1462`). -/
theorem node_app_u3A_regen_u2D_tails_of_deps
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    node_app_u3A_regen_u2D_tailsStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨lG, hlG, hrG, hG⟩ := External.gantert_regeneration_tail d hd Λ₀ r₀
  obtain ⟨lT, hlT, _, hT⟩ := htransfer d hd Λ₀ r₀
  refine ⟨max lG lT, hlG.trans_le (le_max_left _ _),
    hrG.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨cG, CG, _, _, hGtail⟩ :=
    hG l ((le_max_left _ _).trans hl) δ hδ₀ hδ₁
  obtain ⟨cD, c, C, η, N, _, hc, hC, _, _, _, htail⟩ :=
    hT l ((le_max_right _ _).trans hl) δ hδ₀ hδ₁
  let B : ℝ := (1 + C) / (1 - Real.exp (-(c / 4)))
  have hB : 0 < B := div_pos (by linarith)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  refine ⟨c, C, c / 4, 2 * B, hc, hC, by positivity, by linarith,
    by positivity, ?_⟩
  intro Q lam h₀ h₁ P K hK
  have hno := (hGtail Q lam h₀ h₁ P K hK).1
  have htau := (htail Q lam h₀ h₁ P K hK).2.1
  have hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).trans_le hno)
  have hm := Work.W5.regeneration_first_exponentialMoment_le_of_tail
    hd Q lam l c C h₀ hc hC K hK.1 htau
  have hmD := Work.W5.regenerationConditioned_exponentialMoment_le_of_annealed
    hd Q lam l (c / 4) (1 / 2) B (by norm_num) K hK.1 hD hno 1 hm
  have he : B / (1 / 2) = 2 * B := by ring
  rw [he] at hmD
  exact ⟨hD, hno, htau,
    hm.trans (ENNReal.ofReal_le_ofReal (by linarith)), hmD⟩

end EinsteinFull.Blueprint
