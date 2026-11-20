import EinsteinFull.Regeneration.StationaryCoefficient

/-!
# Local ellipticity of normalized weighted coefficients

A positive scalar weight with local upper and lower bounds preserves uniform
ellipticity after a constant normalization.
-/

open MeasureTheory Set

namespace EinsteinFull.Regeneration

/-- A bounded positive weight gives a normalized elliptic coefficient field. -/
theorem normalized_weighted_ellipticity {d : ℕ} (U : Set (PDE.Vec d))
    (a : PDE.CoeffField d) (w : PDE.Vec d → ℝ) (lam Λ m M : ℝ)
    (hlam : 0 < lam) (hm : 0 < m)
    (hmeas : ∀ i j, AEMeasurable (fun x => a x i j) (volume.restrict U))
    (hwmeas : AEMeasurable w (volume.restrict U))
    (hell : ∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x))
    (hw : ∀ᵐ x ∂(volume.restrict U), m ≤ w x ∧ w x ≤ M) :
    (∀ i j, AEMeasurable (fun x => ((m * lam)⁻¹ * w x) * a x i j)
      (volume.restrict U)) ∧
    (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix 1
      ((m * lam)⁻¹ * (M * Λ)) (((m * lam)⁻¹ * w x) • a x)) := by
  have hml : 0 < m * lam := mul_pos hm hlam
  have hc : 0 < (m * lam)⁻¹ := inv_pos.mpr hml
  refine ⟨fun i j => (aemeasurable_const.mul hwmeas).mul (hmeas i j), ?_⟩
  filter_upwards [hell, hw] with x ha hwx
  have hwpos : 0 < w x := hm.trans_le hwx.1
  have hΛ : 0 < Λ := ha.Lam_pos
  have hscale := PDE.isEllipticMatrix_smul (mul_pos hc hwpos) ha
  apply hscale.mono (by norm_num)
  · have hh : (m * lam)⁻¹ * (m * lam) ≤ (m * lam)⁻¹ * (w x * lam) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwx.1 hlam.le) hc.le
    rw [inv_mul_cancel₀ hml.ne'] at hh
    nlinarith
  · have hh : (m * lam)⁻¹ * (w x * Λ) ≤ (m * lam)⁻¹ * (M * Λ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwx.2 hΛ.le) hc.le
    nlinarith

end EinsteinFull.Regeneration
