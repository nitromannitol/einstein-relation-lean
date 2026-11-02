import EinsteinFull.Blueprint.G1.Draft.SbxCManyCycleUniformR06
import EinsteinFull.Blueprint.G1.Draft.SbxCMRenewalUniformR06

/-! Conditional renewal consumers for the proposed Section 3 switch. -/

namespace EinsteinFull.Blueprint.SbxCSwitchRenewalConsumersR15

/-- Uniform many-cycle moments from the ordered graph predecessors. -/
theorem manyCycle_of_deps
    (hfac : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    SbxCManyCycleUniformR06.manyCycleSmoothStmt :=
  SbxCManyCycleUniformR06.manyCycleSmooth_of_deps hfac htails htransfer

/-- Uniform m-renewal from the ordered graph predecessors. Global geometry remains
an explicit graph predecessor although the existing factorization proof subsumes it. -/
@[nolint unusedArguments]
theorem mRenewal_of_deps
    (hfac : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    (_hgeom : node_rt_u3A_global_u2D_geometryStmt) :
    SbxCMRenewalUniformR06.phaseMRenewalSmoothStmt :=
  SbxCMRenewalUniformR06.mRenewal_of_smooth_factorization hfac

end EinsteinFull.Blueprint.SbxCSwitchRenewalConsumersR15
