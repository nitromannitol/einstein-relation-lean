import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_bootstrap_u2D_point

namespace EinsteinFull.Blueprint

/-- The bootstrap closure at `paper/main.tex:770–774` supplies the complete
scalar conclusion at `paper/main.tex:626–645`, with the structural witnesses
already chosen before the moment order. -/
theorem node_p_u3A_scalar_of_deps
    (hbootstrap : node_p_u3A_scalar_u23_bootstrap_u2D_pointStmt) :
    node_p_u3A_scalarStmt :=
  hbootstrap

end EinsteinFull.Blueprint
