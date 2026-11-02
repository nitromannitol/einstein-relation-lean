import EinsteinFull.Blueprint.G3.node_e_u3A_parameters
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_test_u2D_replacement
import EinsteinFull.Calculus.C2TestReplacementSupport

open MeasureTheory
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinFull.Calculus.C2TestReplacement

/-- Smooth-test replacement at the literal dyadic mesoscopic radius. -/
theorem node_p_u3A_covariance_u23_test_u2D_replacement_of_deps
    (_hparameters : node_e_u3A_parametersStmt)
    (hclt : node_e_u3A_test_u2D_cltStmt)
    (hcoarse : node_p_u3A_covariance_u23_coarse_u2D_identificationStmt)
    (hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt) :
    node_p_u3A_covariance_u23_test_u2D_replacementStmt := by
  intro d hd D s δ γ η β h N hN
  obtain ⟨θ, hθ, hθone, hθγ, hθη⟩ := exists_theta d hd D s δ γ η β h
  have hη : 0 < η := by
    rcases h with ⟨_, _, _, _, _, _, _, _, hη, _, _⟩
    linarith
  obtain ⟨R₀, hR₀, hrange⟩ := exists_physical_threshold D.dependenceRange θ η hθ hη
  obtain ⟨C₁, hC₁, hb₁⟩ := scaledJointPairing_smoothed_error_bound hclt d hd D N hN
  obtain ⟨C₂, hC₂, hb₂⟩ := smoothedPairing_localized_bound hcoarse hloc
    d hd D s δ γ η β h N (by omega)
  refine ⟨θ, max C₁ C₂, R₀, hθ, hθone, hθγ, hθη,
    hC₁.trans_le (le_max_left _ _), hR₀, ?_⟩
  intro Q hQ Z hZ R hR hRlarge F
  let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
  let r := L ^ η
  have hRpos : 0 < R := by linarith
  have hFn : 0 ≤ schwartzTestNorm N F := clockSchwartz_norm_nonneg N F
  have hr : 0 < r := Real.rpow_pos_of_pos (zpow_pos (by norm_num) _) _
  have hrange' : 2 * D.dependenceRange ≤ r := hrange R hRlarge
  obtain ⟨hsmooth, hlocal, hsecond⟩ := hb₂ Q hQ Z hZ r hrange' R hRpos F
  refine ⟨hrange', hsmooth, hlocal, ?_, ?_⟩
  · exact (hb₁ Q hQ Z hZ R hRpos F r hr).trans (by
      gcongr
      exact le_max_left C₁ C₂)
  · exact hsecond.trans (by
      gcongr
      exact le_max_right C₁ C₂)

end EinsteinFull.Blueprint
