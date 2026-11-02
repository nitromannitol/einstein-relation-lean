import EinsteinFull.Blueprint.G1.Draft.SbxCSwitchContractsR17
import EinsteinFull.Blueprint.Roots.Draft.SbxCSwitchRootsR15
import EinsteinFull.Blueprint.Roots.Draft.SbxCSwitchFactorizationR15
import EinsteinFull.Blueprint.Roots.Draft.SbxCTailRootR01
import EinsteinFull.Blueprint.Roots.node_rt_u3A_local_u2D_mixingV2
import EinsteinFull.Blueprint.Roots.node_rt_u3A_renewalV2
import EinsteinFull.Blueprint.Roots.node_app_u3A_factorizationV2
import EinsteinFull.Blueprint.Roots.node_rt_u3A_factorizationV2

/-! Section 3 switch (2026-11-01): exact root reductions of the four restated numbered results and of the
frozen `p:tail` from the full-range tail sum. -/

namespace EinsteinFull.Blueprint


/-- The signed full-range k/m decomposition implies local mixing. -/
theorem node_rt_u3A_local_u2D_mixing_of_depsV2
    (hkm : node_rt_u3A_km_u2D_decompStmtV4) :
    node_rt_u3A_local_u2D_mixingStmtV2 :=
  SbxCSwitchRootsR15.localMixing_of_deps hkm

/-- The original Cauchy and transfer nodes and the smooth uniform many-cycle
moment node imply the smooth uniform renewal statement. -/
theorem node_rt_u3A_renewal_of_depsV2
    (hcauchy : node_rt_u3A_renewal_u23_cauchyStmt)
    (hmoments : node_rt_u3A_many_u2D_cycle_u2D_momentStmtV2)
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    node_rt_u3A_renewalStmtV2 :=
  SbxCSwitchRootsR15.renewal_of_deps hcauchy hmoments htransfer



/-- The reviewed appendix root from its three ordered graph dependencies. -/
@[nolint unusedArguments]
theorem node_app_u3A_factorization_of_depsV2
    (_hindependence : node_app_u3A_factorization_u23_independenceStmtV2)
    (hiterate : node_app_u3A_factorization_u23_condition_u2D_iterateStmt)
    (_hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt) :
    node_app_u3A_factorizationStmtV2 := by
  intro d hd D Q _hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
  exact (hiterate d hd D.ellipticity D.dependenceRange Q lam h₀ h₁ l δ
    hl hsep hδ₀ hδ₁ P K hK hD).2.2

/-- The reviewed environmental root from its five ordered graph dependencies. -/
theorem node_rt_u3A_factorization_of_depsV2
    (hfactor : node_app_u3A_factorizationStmtV2)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hsmall : node_rt_u3A_factorization_u23_small_u2D_indicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt) :
    node_rt_u3A_factorizationStmtV2 := by
  apply SbxCFactorizationR01.environmentalFactorizationSmooth_of_deps hfactor
    (SbxCFactorizationR01.pastKernelSmooth_of_original hpast)
    (SbxCFactorizationR01.slicesSmooth_of_original hslices) hsmall
  intro d hd D Q _hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
  exact hscope d hd D.ellipticity D.dependenceRange Q lam h₀ h₁ l δ
    hl hsep hδ₀ hδ₁ P K hK hD


/-- The frozen `p:tail` from the full-range tail summation. -/
theorem node_p_u3A_tail_of_depsV2
    (hsum : node_p_u3A_tail_u23_sumStmtV2) :
    node_p_u3A_tailStmt :=
  node_p_u3A_tail_of_deps hsum

end EinsteinFull.Blueprint
