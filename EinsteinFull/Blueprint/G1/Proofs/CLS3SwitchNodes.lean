import EinsteinFull.Blueprint.Roots.node_rt_u3A_local_u2D_mixingV2
import EinsteinFull.Blueprint.Roots.node_rt_u3A_renewalV2
import EinsteinFull.Blueprint.Roots.node_app_u3A_factorizationV2
import EinsteinFull.Blueprint.Roots.node_rt_u3A_factorizationV2
import EinsteinFull.Blueprint.G1.Draft.SbxCSwitchContractsR17
import EinsteinFull.Blueprint.G1.Draft.SbxCSwitchRenewalConsumersR15
import EinsteinFull.Blueprint.G1.Draft.SbxCSwitchPhaseFixedR15
import EinsteinFull.Blueprint.G4.Draft.SbxCSwitchTailR15

/-! Section 3 switch (2026-11-01): exact graph reductions of the reviewed internal contracts. -/

namespace EinsteinFull.Blueprint

/-- Ordered predecessors for the reviewed many-cycle contract. -/
theorem node_rt_u3A_many_u2D_cycle_u2D_moment_v2_of_deps
    (hfac : node_rt_u3A_factorizationStmtV2)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    node_rt_u3A_many_u2D_cycle_u2D_momentStmtV2 :=
  SbxCSwitchRenewalConsumersR15.manyCycle_of_deps hfac htails htransfer

/-- Ordered predecessors for the reviewed m-renewal contract. -/
theorem node_rt_u3A_m_u2D_renewal_v2_of_deps
    (hfac : node_rt_u3A_factorizationStmtV2)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt) :
    node_rt_u3A_m_u2D_renewalStmtV2 :=
  SbxCSwitchRenewalConsumersR15.mRenewal_of_deps hfac hgeom

/-- Ordered predecessors for the reviewed fixed-radius contract. -/
theorem node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radius_v4_of_deps
    (hfact : node_rt_u3A_factorizationStmtV2)
    (hren : node_rt_u3A_renewalStmtV2)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt) :
    node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmtV4 :=
  SbxCSwitchPhaseFixedR15.fixedRadius_of_deps hfact hren hrem htails

/-- Ordered predecessors for the reviewed phase-error contract. -/
theorem node_rt_u3A_local_u2D_mixing_u23_phase_u2D_error_v4_of_deps
    (hmren : node_rt_u3A_m_u2D_renewalStmtV2)
    (hren : node_rt_u3A_renewalStmtV2)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (hfixed : node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmtV4) :
    node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmtV4 :=
  SbxCSwitchPhaseFixedR15.phase_of_deps hmren hren hrem hfixed

/-- Ordered predecessors for the reviewed full-range tail summation. -/
theorem node_p_u3A_tail_u23_sum_v2_of_deps
    (hsmall : node_p_u3A_tail_u23_small_u2D_endpointsStmt)
    (hann : node_p_u3A_tail_u23_annuliStmt)
    (hLM : node_rt_u3A_local_u2D_mixingStmtV2) :
    node_p_u3A_tail_u23_sumStmtV2 :=
  SbxCSwitchTailR15.tailSum_of_deps hsmall hann hLM

end EinsteinFull.Blueprint
