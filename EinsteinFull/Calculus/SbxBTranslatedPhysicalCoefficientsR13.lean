import EinsteinFull.Calculus.SbxS4KilledSpectralR01
import EinsteinRelation.Environment.ActualImageLpTransportSupport

namespace EinsteinFull.Calculus

open EinsteinRelation
open EinsteinRelation.External.GantertSection7Support

/-- Translation preserves all regularity conditions with the same constant. -/
theorem b_translated_isRegular {d : ℕ} {L : ℝ} (ω : FieldPair d)
    (hω : IsRegular L ω) (c : Vec d) : IsRegular L (translate c ω) :=
  (ActualImageLpStateTransport.isRegular_translate_iff c ω).2 hω

/-- The exact physical reversible-density factor under translation. -/
theorem b_translated_physical_rho {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (c z : Vec d) :
    s4PhysicalRho hd ω lam (c + z) =
      physicalForceWeight hd lam c * s4PhysicalRho hd (translate c ω) lam z := by
  simp only [s4PhysicalRho, physicalReversibleDensity_eq_source_formula,
    physicalForceWeight, translate_scalar, Pi.add_apply, ← Real.exp_add]
  congr 1
  ring

/-- The divergence coefficient transforms by the same scalar factor. -/
theorem b_translated_physical_alpha {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (c z : Vec d) :
    s4PhysicalAlpha hd ω lam (c + z) =
      physicalForceWeight hd lam c • s4PhysicalAlpha hd (translate c ω) lam z := by
  rw [s4PhysicalAlpha, s4PhysicalAlpha, b_translated_physical_rho]
  simp only [translate_matrix, smul_smul]
  congr 1
  ring

end EinsteinFull.Calculus

