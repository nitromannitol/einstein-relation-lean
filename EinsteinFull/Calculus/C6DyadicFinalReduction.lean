import EinsteinFull.Calculus.C6DyadicConditionalAssembly
import EinsteinFull.Calculus.C2DyadicForceWindowDensity
import EinsteinFull.Calculus.C4DyadicTransposeEndpointDecay

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem node_p_u3A_late_u23_dyadic_u2D_increments_of_deps
    (henergy : node_e_u3A_energy_u2D_targetStmt)
    (hlocal : node_l_u3A_forced_u2D_localStmt)
    (hflux : node_e_u3A_time_u2D_fluxStmt) :
    node_p_u3A_late_u23_dyadic_u2D_incrementsStmt := by
  exact c6_dyadic_increments_of_density_increment_bound
    (c2_dyadic_density_from_unit_window_endpoint hlocal
      (c4_dyadic_transpose_endpoint_decay hlocal)) henergy hlocal hflux

end EinsteinFull.Blueprint
