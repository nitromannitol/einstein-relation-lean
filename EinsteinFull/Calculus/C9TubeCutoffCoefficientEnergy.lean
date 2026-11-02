import EinsteinFull.External.Source.GMPDirichletKernel

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The elliptic coefficient energy of a sum is bounded using Euclidean squares. -/
theorem c9_cutoff_coefficient_energy_bound {d : ℕ}
    (κ : ℝ) (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (x : Vec d)
    (a b : ℝ) (v w : Vec d) :
    dot ((α x).mulVec (a • v + b • w)) (a • v + b • w) ≤
      2 * κ⁻¹ * (a^2 * euclideanSq v + b^2 * euclideanSq w) := by
  have hs : euclideanSq (a • v + b • w) ≤
      2 * (a^2 * euclideanSq v + b^2 * euclideanSq w) := by
    calc
      euclideanSq (a • v + b • w) ≤
          ∑ i : Fin d, 2 * ((a * v i)^2 + (b * w i)^2) := by
        simp only [euclideanSq, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_le_sum fun i _ => ?_
        nlinarith [sq_nonneg (a * v i - b * w i)]
      _ = 2 * (a^2 * euclideanSq v + b^2 * euclideanSq w) := by
        unfold euclideanSq dot
        conv_rhs => rw [mul_add]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hu := (hell.2.2 x).2.2.2 (a • v + b • w)
  have hcomm : dot ((α x).mulVec (a • v + b • w)) (a • v + b • w) =
      dot (a • v + b • w) ((α x).mulVec (a • v + b • w)) := by
    simp only [dot, mul_comm]
  rw [hcomm]
  calc
    _ ≤ κ⁻¹ * euclideanSq (a • v + b • w) := hu.2
    _ ≤ κ⁻¹ * (2 * (a^2 * euclideanSq v + b^2 * euclideanSq w)) :=
      mul_le_mul_of_nonneg_left hs (le_of_lt (inv_pos.mpr hκ))
    _ = _ := by ring

/-- Integrating the coefficient bound requires only measurability and bounds for
    the two Euclidean-square summands. -/
theorem c9_cutoff_coefficient_energy_lintegral {d : ℕ}
    (κ : ℝ) (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (μ : Measure (ℝ × Vec d)) (a b : ℝ × Vec d → ℝ)
    (v w : ℝ × Vec d → Vec d) (A B : ℝ≥0∞)
    (hm : AEMeasurable (fun z => ENNReal.ofReal (a z ^ 2 * euclideanSq (v z))) μ)
    (hmB : AEMeasurable (fun z => ENNReal.ofReal (b z ^ 2 * euclideanSq (w z))) μ)
    (hA : (∫⁻ z, ENNReal.ofReal (a z ^ 2 * euclideanSq (v z)) ∂μ) ≤ A)
    (hB : (∫⁻ z, ENNReal.ofReal (b z ^ 2 * euclideanSq (w z)) ∂μ) ≤ B) :
    (∫⁻ z, ENNReal.ofReal (dot ((α z.2).mulVec (a z • v z + b z • w z))
      (a z • v z + b z • w z)) ∂μ) ≤ ENNReal.ofReal (2 * κ⁻¹) * (A + B) := by
  have hv (z : ℝ × Vec d) : 0 ≤ a z ^ 2 * euclideanSq (v z) := by
    apply mul_nonneg (sq_nonneg _)
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hw (z : ℝ × Vec d) : 0 ≤ b z ^ 2 * euclideanSq (w z) := by
    apply mul_nonneg (sq_nonneg _)
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (2 * κ⁻¹) *
        (ENNReal.ofReal (a z ^ 2 * euclideanSq (v z)) +
          ENNReal.ofReal (b z ^ 2 * euclideanSq (w z))) ∂μ := by
      apply lintegral_mono
      intro z
      have h := ENNReal.ofReal_le_ofReal
        (c9_cutoff_coefficient_energy_bound κ hκ ρ α hell z.2 (a z) (b z) (v z) (w z))
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (hv z) (hw z)] at h
      exact h
    _ = ENNReal.ofReal (2 * κ⁻¹) *
        ((∫⁻ z, ENNReal.ofReal (a z ^ 2 * euclideanSq (v z)) ∂μ) +
          (∫⁻ z, ENNReal.ofReal (b z ^ 2 * euclideanSq (w z)) ∂μ)) := by
      change (∫⁻ z, ENNReal.ofReal (2 * κ⁻¹) *
        ((fun z => ENNReal.ofReal (a z ^ 2 * euclideanSq (v z))) +
          (fun z => ENNReal.ofReal (b z ^ 2 * euclideanSq (w z)))) z ∂μ) = _
      rw [lintegral_const_mul'' _ (hm.add hmB)]
      simp only [Pi.add_apply]
      rw [lintegral_add_left' hm]
    _ ≤ _ := by gcongr

/-- The cutoff-power gradient energy, with both square terms controlled. -/
theorem c9_small_power_cutoff_coefficient_energy_lintegral {d : ℕ}
    (κ : ℝ) (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (μ : Measure (ℝ × Vec d)) (η u : ℝ × Vec d → ℝ)
    (G : ℝ × Vec d → Vec d) (p : ℝ) (A B : ℝ≥0∞)
    (hmA : AEMeasurable (fun z => ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (u z) ^ (p / 2 - 1)) • G z))) μ)
    (hmB : AEMeasurable (fun z => ENNReal.ofReal
      (((u z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j)))) μ)
    (hA : (∫⁻ z, ENNReal.ofReal
      (η z ^ 2 * euclideanSq ((p / 2 * (u z) ^ (p / 2 - 1)) • G z)) ∂μ) ≤ A)
    (hB : (∫⁻ z, ENNReal.ofReal
      (((u z) ^ (p / 2)) ^ 2 * euclideanSq (fun j => fderiv ℝ η z (0, unitVector j))) ∂μ) ≤ B) :
    (∫⁻ z, ENNReal.ofReal (dot
      ((α z.2).mulVec (η z • ((p / 2 * (u z) ^ (p / 2 - 1)) • G z) +
        (u z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))))
      (η z • ((p / 2 * (u z) ^ (p / 2 - 1)) • G z) +
        (u z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j)))) ∂μ) ≤ ENNReal.ofReal (2 * κ⁻¹) * (A + B) :=
  c9_cutoff_coefficient_energy_lintegral κ hκ ρ α hell μ η
    (fun z => (u z) ^ (p / 2))
    (fun z => (p / 2 * (u z) ^ (p / 2 - 1)) • G z) (fun z j => fderiv ℝ η z (0, unitVector j)) A B hmA hmB hA hB

end EinsteinFull.Calculus
