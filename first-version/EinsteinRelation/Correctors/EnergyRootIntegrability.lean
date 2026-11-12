import EinsteinRelation.Correctors.WeightedEnergyFromIntegral

/-! # Integrability of a scalar energy root at zero

Source: `paper/main.tex:824–840`. A continuous extension of the literal
positive-time energy makes its root integrable, independently of the
chosen value of the actual flow at time zero.
-/

open MeasureTheory Set
namespace EinsteinRelation.Correctors

/-- A continuous realization of the actual positive-time energy supplies
its scalar source integrability. Source: `paper/main.tex:824–840`. -/
theorem energy_root_integrable_of_continuous_extension
    {A F : ℝ → ℝ} {T : ℝ} (n : ℕ)
    (hF : ContinuousOn F (Icc 0 T))
    (hrep : ∀ t : ℝ, 0 < t → t ≤ T → F t = A t) :
    IntegrableOn (fun t => (A t)^((n : ℝ)⁻¹)) (Icc 0 T) := by
  have hi : IntegrableOn (fun t => (F t)^((n : ℝ)⁻¹)) (Icc 0 T) := ((Real.continuous_rpow_const
    (inv_nonneg.mpr (Nat.cast_nonneg n))).comp_continuousOn hF).integrableOn_Icc
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht hne
  rw [hrep t (lt_of_le_of_ne ht.1 (Ne.symm hne)) ht.2]

end EinsteinRelation.Correctors
