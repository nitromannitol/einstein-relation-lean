import EinsteinFull.Calculus.SbxBTubeExactReductionR15
import EinsteinFull.Calculus.SbxAExactScopeReductionR13

/-!
# Section 3 reductions: tube probability and coupling scope

The exact graph reductions of `rt:renewal#tube-probability` and
`app:factorization#coupling-scope`. The tube lower bound is proved inside the project, from the
admitted inputs and the elliptic and process libraries, with no further literature input.
-/

namespace EinsteinFull.Blueprint

/-- `rt:renewal#tube-probability` from its ordered graph hypotheses. -/
theorem node_rt_u3A_renewal_u23_tube_u2D_probability_of_deps
    (hgeom : node_rt_u3A_renewal_u23_tube_u2D_geometryStmt)
    (hbounds : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt :=
  b_tube_probability_of_deps_r15 hgeom hbounds

/-- `app:factorization#coupling-scope` from its ordered graph hypothesis. -/
theorem node_app_u3A_factorization_u23_coupling_u2D_scope_of_deps
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt :=
  a_coupling_scope_of_deps_r13 htails

end EinsteinFull.Blueprint
