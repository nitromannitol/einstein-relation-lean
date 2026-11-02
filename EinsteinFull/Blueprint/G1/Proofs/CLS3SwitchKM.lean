import EinsteinFull.Calculus.SbxAExactKMReductionR13

/-! Section 3 switch (2026-11-01): exact graph reduction of the reviewed signed k/m contract. -/

namespace EinsteinFull.Blueprint

/-- Ordered predecessors for the reviewed signed k/m contract. -/
theorem node_rt_u3A_km_u2D_decomp_of_deps
    (hfactor : node_rt_u3A_k_u2D_factorStmt)
    (hphase : node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV4)
    (hmany : node_rt_u3A_many_u2D_cycle_u2D_momentStmtV2)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    node_rt_u3A_km_u2D_decompStmtV4 :=
  a_km_decomp_of_deps_r13 hfactor hphase hmany hrem

end EinsteinFull.Blueprint
