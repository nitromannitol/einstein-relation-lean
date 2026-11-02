import EinsteinFull.Calculus.SbxAOriginalScopeSourceR08
import EinsteinFull.Calculus.SbxBCouplingSetwiseLowerR12
import EinsteinFull.Calculus.SbxBCenteredSurvivalClosureR15

/-! The original coupling scope follows from the regeneration tails. -/

namespace EinsteinFull.Blueprint

/-- Regeneration tails imply the original coupling scope for regular laws. -/
theorem a_coupling_scope_of_deps_r13
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt :=
  s1_original_scope_of_setwise_lower_and_tube htails
    EinsteinFull.b_original_setwise_lower
    EinsteinFull.b_centered_survival_unconditional_r15

#print axioms a_coupling_scope_of_deps_r13
#print a_coupling_scope_of_deps_r13

end EinsteinFull.Blueprint
