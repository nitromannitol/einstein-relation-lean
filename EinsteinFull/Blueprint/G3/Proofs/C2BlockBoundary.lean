import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_boundary
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_joint_u2D_localization
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_clock_u2D_blocks
import EinsteinFull.Calculus.C2BlockBoundarySupport

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull.Calculus.C2BlockBoundary

/-- Boundary-strip control of the actual physical matrix-clock block. -/
theorem node_e_u3A_block_u2D_boundary_of_deps
    (_hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (_hclock : node_p_u3A_covariance_u23_clock_u2D_blocksStmt) :
    node_e_u3A_block_u2D_boundaryStmt := by
  intro d hd D s δ γ η β h
  obtain ⟨C, L₀, hC, hL₀, hb⟩ := covarianceBlock_boundary_L2 d hd D s δ γ η β h
  exact ⟨C, L₀, hC, hL₀, fun Q _ => hb Q⟩

end EinsteinFull.Blueprint
