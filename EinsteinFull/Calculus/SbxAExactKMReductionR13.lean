import EinsteinFull.Calculus.SbxAKMFinalAssemblerR12
import EinsteinFull.Calculus.SbxBCouplingSetwiseLowerR12

noncomputable section

namespace EinsteinFull.Blueprint

/-- The signed k/m contract from its four canonical predecessors. -/
theorem a_km_decomp_of_deps_r13
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV4)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmtV2)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    node_rt_u3A_km_u2D_decompStmtV4 :=
  a_km_decomp_of_deps_and_setwise_r12 hfactor hphase hmany hrem
    EinsteinFull.b_original_setwise_lower

#check a_km_decomp_of_deps_r13
#print axioms a_km_decomp_of_deps_r13

end EinsteinFull.Blueprint
