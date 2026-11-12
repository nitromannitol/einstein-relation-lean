import EinsteinRelation.Correctors.FractionalIntegralInterpolation
import EinsteinRelation.Correctors.CutoffHolderPowerIdentity

/-! # Spatial interpolation for the paired weighted energy

Source: `paper/main.tex:824–832`. Hölder interpolation controls the exact
cutoff error by the weighted and unweighted scalar energies. The same
lemma applies to a normalized spatial measure.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Integrability and the spatial Hölder estimate for the literal cutoff
error, with no division by the scalar energy. Source: `paper/main.tex:826–831`. -/
theorem integral_cutoff_error_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {χ v : X → ℝ} (hχ : Measurable χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hv : MemLp v 2 μ)
    (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun x => χ x ^ (2 * n - 2) * v x ^ 2) μ ∧
      (∫ x, χ x ^ (2 * n - 2) * v x ^ 2 ∂μ) ≤
        (∫ x, χ x ^ (2 * n) * v x ^ 2 ∂μ) ^ (1 - (n : ℝ)⁻¹) *
          (∫ x, v x ^ 2 ∂μ) ^ ((n : ℝ)⁻¹) := by
  have hpower (k : ℕ) : ∀ x, ‖χ x ^ k‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hχb x).1 k)]
    exact pow_le_one₀ (hχb x).1 (hχb x).2
  have hi (k : ℕ) : Integrable (fun x => χ x ^ k * v x ^ 2) μ :=
    hv.integrable_sq.bdd_mul (hχ.pow_const k).aestronglyMeasurable
      (Filter.Eventually.of_forall (hpower k))
  refine ⟨hi _, ?_⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : (n : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := integral_rpow_mul_rpow_le μ (p := 1 - (n : ℝ)⁻¹)
    (by linarith) (by linarith)
    (fun x => mul_nonneg (pow_nonneg (hχb x).1 _) (sq_nonneg _))
    (fun x => sq_nonneg (v x)) (hi (2 * n)) hv.integrable_sq
  simp only [sub_sub_cancel] at h
  convert h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => cutoff_holder_rpow_identity (hχb x).1 n hn

end EinsteinRelation.Correctors
