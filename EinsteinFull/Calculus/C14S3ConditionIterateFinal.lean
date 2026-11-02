import EinsteinFull.Calculus.U5SelfAdjointSemigroupAnalytic
import EinsteinFull.Calculus.SunaS6KilledAnalytic
import EinsteinFull.Calculus.C14S3ConditionIterateAssembly

namespace EinsteinFull.Blueprint

/-- The condition-iterate node follows from its three graph dependencies. -/
theorem node_app_u3A_factorization_u23_condition_u2D_iterate_of_deps
    (h1 : node_app_u3A_factorization_u23_independenceStmtV2)
    (h2 : node_app_u3A_factorization_u23_slicesStmt)
    (h3 : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt := by
  exact c14_s3_condition_iterate_of_requested_killed_analytic
    (s6_requested_killed_orbit_analytic_of_semigroup_analytic.{0}
      u5_symmetric_contraction_semigroup_scalar_analytic) h1 h2 h3

#print node_app_u3A_factorization_u23_condition_u2D_iterate_of_deps
#print axioms node_app_u3A_factorization_u23_condition_u2D_iterate_of_deps

end EinsteinFull.Blueprint
