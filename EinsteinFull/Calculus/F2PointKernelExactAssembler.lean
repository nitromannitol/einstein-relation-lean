import EinsteinFull.Calculus.SunaS3PointKernelAssembly

namespace EinsteinFull.Blueprint

/-- The point-kernel bound follows from its three original dependencies. -/
theorem node_l_u3A_forced_u2D_local_u23_point_u2D_kernel_of_deps :
    node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt →
    node_e_u3A_local_u2D_timeStmt →
    node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt →
    node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt :=
  EinsteinFull.s3_point_kernel_of_global_interpolation

end EinsteinFull.Blueprint
