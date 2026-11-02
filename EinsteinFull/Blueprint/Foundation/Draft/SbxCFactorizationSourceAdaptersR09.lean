import EinsteinFull.Blueprint.Foundation.Draft.SbxCFactorizationSmoothR01
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices

namespace EinsteinFull.Blueprint.SbxCFactorizationR01

/-- The original past-kernel statement specializes to smooth environment laws. -/
theorem pastKernelSmooth_of_original
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt) :
    pastKernelSmoothStmt := by
  intro d hd D Q _hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  exact hpast d hd D.ellipticity D.dependenceRange Q lam h₀ h₁ l δ
    hl hsep hδ₀ hδ₁ P K hK

/-- The original slice statement specializes to smooth environment laws. -/
theorem slicesSmooth_of_original
    (hslices : node_app_u3A_factorization_u23_slicesStmt) :
    slicesSmoothStmt := by
  intro d hd D Q _hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  exact hslices d hd D.ellipticity D.dependenceRange Q lam h₀ h₁ l δ
    hl hsep hδ₀ hδ₁ P K hK

end EinsteinFull.Blueprint.SbxCFactorizationR01
