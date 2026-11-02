import EinsteinFull.Blueprint.Roots.Draft.SbxCFactorizationRootsR01
import EinsteinFull.Blueprint.Foundation.Draft.SbxCFactorizationSourceAdaptersR09

namespace EinsteinFull.Blueprint.SbxCSwitchFactorizationR15

/-- The original factorization dependencies yield the smooth-law appendix result. -/
@[nolint unusedArguments]
theorem appendixFactorization_of_deps
    (_hindependence : node_app_u3A_factorization_u23_independenceStmtV2)
    (hiterate : node_app_u3A_factorization_u23_condition_u2D_iterateStmt)
    (_hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt) :
    SbxCFactorizationR01.appendixFactorizationSmoothStmt := by
  intro d hd D Q _hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
  exact (hiterate d hd D.ellipticity D.dependenceRange Q lam h₀ h₁ l δ
    hl hsep hδ₀ hδ₁ P K hK hD).2.2

/-- The original locality, slice and coupling-scope dependencies specialize to
smooth laws for the environmental factorization. -/
theorem environmentalFactorization_of_deps
    (hfactor : SbxCFactorizationR01.appendixFactorizationSmoothStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hslices : node_app_u3A_factorization_u23_slicesStmt)
    (hsmall : node_rt_u3A_factorization_u23_small_u2D_indicesStmt)
    (hscope : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt) :
    SbxCFactorizationR01.environmentalFactorizationSmoothStmt := by
  apply SbxCFactorizationR01.environmentalFactorizationSmooth_of_deps hfactor
    (SbxCFactorizationR01.pastKernelSmooth_of_original hpast)
    (SbxCFactorizationR01.slicesSmooth_of_original hslices) hsmall
  intro d hd D Q _hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
  exact hscope d hd D.ellipticity D.dependenceRange Q lam h₀ h₁ l δ
    hl hsep hδ₀ hδ₁ P K hK hD

end EinsteinFull.Blueprint.SbxCSwitchFactorizationR15
