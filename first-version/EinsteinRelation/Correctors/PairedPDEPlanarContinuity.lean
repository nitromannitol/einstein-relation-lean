import EinsteinRelation.Correctors.PairedPDEPlanarRotation
import Mathlib.Topology.Instances.Matrix

/-! # Continuity of the planar dual coefficient

Source: `paper/main.tex:877–883`. Continuous elliptic coefficients have
continuous inverse coefficients. Thus the manuscript's dual coefficient
has genuine spatial measurability whenever the original coefficient is
continuous, as it is under the standing Lipschitz assumption.
-/

namespace EinsteinRelation.Correctors

/-- The inverse of a continuous elliptic field is continuous; ellipticity
supplies invertibility rather than an extra premise.
Source: `paper/main.tex:877–883`. -/
theorem continuous_inverse_of_isElliptic {d : ℕ} {L : ℝ} (hL : 0 < L)
    {a : Vec d → Mat d} (ha : IsElliptic L a) (hc : Continuous a) :
    Continuous (fun x => (a x)⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (hc.matrix_det.inv₀ (fun x => (isUnit_iff_ne_zero.mp
    (isElliptic_isUnit_det hL ha x)))).smul hc.matrix_adjugate

/-- The actual planar dual coefficient is continuous, hence spatially
measurable, for a continuous elliptic original field.
Source: `paper/main.tex:877–883`. -/
theorem continuous_planar_dual {L : ℝ} (hL : 0 < L)
    {a : Vec 2 → Mat 2} (ha : IsElliptic L a) (hc : Continuous a) :
    Continuous (fun x => planarRotation * (a x)⁻¹ * planarRotation.transpose) :=
  (continuous_const.matrix_mul (continuous_inverse_of_isElliptic hL ha hc)).matrix_mul
    continuous_const

end EinsteinRelation.Correctors
