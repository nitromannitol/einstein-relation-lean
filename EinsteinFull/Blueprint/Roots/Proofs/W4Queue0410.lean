import EinsteinFull.Blueprint.Roots.node_p_u3A_covariance
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_closure

namespace EinsteinFull.Blueprint

/-- The covariance closure supplies the complete all-scale comparison of
`paper/main.tex:864–871`, including complex bilinear tests. -/
theorem node_p_u3A_covariance_of_deps
    (hclosure : node_p_u3A_covariance_u23_closureStmt) :
    node_p_u3A_covarianceStmt :=
  hclosure

end EinsteinFull.Blueprint
