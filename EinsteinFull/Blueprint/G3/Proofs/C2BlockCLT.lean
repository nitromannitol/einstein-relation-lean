import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_clt
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_joint_u2D_localization
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_clock_u2D_blocks
import EinsteinFull.Calculus.C2BlockCLTSupport

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull.Calculus.C2BlockCLT

/-- Uniform CLT-order control of the actual physical matrix-clock block. -/
theorem node_e_u3A_block_u2D_clt_of_deps
    (_hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (_hclock : node_p_u3A_covariance_u23_clock_u2D_blocksStmt) :
    node_e_u3A_block_u2D_cltStmt := by
  intro d hd D s δ γ η β h
  obtain ⟨C, L₀, hC, hL₀, hb⟩ := covarianceBlock_clt_L2 d hd D s δ γ η β h
  exact ⟨C, L₀, hC, hL₀, fun Q _ => hb Q⟩

end EinsteinFull.Blueprint
