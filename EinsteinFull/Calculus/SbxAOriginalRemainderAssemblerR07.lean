import EinsteinFull.Calculus.SbxAGMPActionAssemblerR07
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeRealSemigroup

/-!
The original remainder graph interface, assembled through the actual GMP action.
The recorded graph interface retains its original ordered dependency arguments;
the action proof makes the real-semigroup argument unnecessary to the proof.
-/

namespace EinsteinFull.Blueprint

/-- Original graph reduction with its recorded ordered dependencies. The actual
GMP action proves the conclusion using the regeneration tails alone. -/
theorem s6_remainder_moment_of_original_deps
    (htail : node_app_u3A_regen_u2D_tailsStmt)
    (_hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2) :
    node_rt_u3A_remainder_u2D_momentStmt :=
  s8_remainder_moment_of_regeneration_tails htail

end EinsteinFull.Blueprint
