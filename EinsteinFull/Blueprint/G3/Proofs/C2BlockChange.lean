import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_change
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_joint_u2D_localization
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_clock_u2D_blocks
import EinsteinFull.Calculus.C2BlockChangeSupport

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull.Calculus.C2BlockChange

/-- Uniform scale change for the actual physical Euclidean matrix-clock block. -/
theorem node_e_u3A_block_u2D_change_of_deps
    (_hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (_hclock : node_p_u3A_covariance_u23_clock_u2D_blocksStmt) :
    node_e_u3A_block_u2D_changeStmt := by
  intro d hd D s δ γ η β h
  obtain ⟨C, L₀, κ, hC, hL₀, hκ, hκβ, hb⟩ := covarianceBlock_change_L2 d hd D s δ γ η β h
  exact ⟨C, L₀, κ, hC, hL₀, hκ, hκβ, fun Q _ => hb Q⟩

end EinsteinFull.Blueprint
