import EinsteinFull.Blueprint.G1.Draft.SbxCLocalMixingUniformR06
import EinsteinFull.Blueprint.G1.Draft.SbxCManyCycleUniformR06
import EinsteinFull.Blueprint.Roots.Draft.SbxCRenewalUniformR06

/-! Conditional root reductions for the Section 3 switch. -/

namespace EinsteinFull.Blueprint.SbxCSwitchRootsR15

/-- Local mixing follows from the uniform full-range k/m decomposition. -/
theorem localMixing_of_deps
    (hkm : SbxCLocalMixingUniformR06.kmDecompUniformFullRangeSmoothStmt) :
    SbxCLocalMixingUniformR06.localMixingUniformFullRangeSmoothStmt :=
  SbxCLocalMixingUniformR06.localMixingUniform_of_km hkm

/-- Renewal follows from the original Cauchy and transfer nodes and the
uniform many-cycle node. -/
theorem renewal_of_deps
    (hcauchy : node_rt_u3A_renewal_u23_cauchyStmt)
    (hmany : SbxCManyCycleUniformR06.manyCycleSmoothStmt)
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    SbxCRenewalUniformR06.renewalUniformStmt := by
  apply SbxCRenewalUniformR06.renewalUniform_of_deps ?_ hmany htransfer
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀, hl₀, hr₀, hc⟩ := hcauchy d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hr₀, ?_⟩
  intro l hl δ hδ hδ₁
  obtain ⟨ρ, B, c, C, hρ, hB, hcpos, hC, hest⟩ := hc l hl δ hδ hδ₁
  refine ⟨ρ, B, c, C, hρ, hB, hcpos, hC, ?_⟩
  intro β hβ
  dsimp only
  intro Q hQ lam h₀ h₁ P K hK hD
  exact hest Q lam h₀ h₁ P K hK hD

end EinsteinFull.Blueprint.SbxCSwitchRootsR15
