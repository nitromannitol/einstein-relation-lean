import EinsteinRelation.Correctors.PairedPDERegularizationDerivative
import Mathlib.MeasureTheory.Integral.Prod

/-! # Exact cancellation of the regularized temporal energy

Source: `paper/main.tex:832–840`. Fubini and antisymmetry cancel the
quadratic pairing with an odd kernel. Even smooth mollifiers therefore
give zero temporal self-pairing without a time derivative of the solution.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- An odd compact kernel has zero quadratic pairing with actual L¹ data.
Source: `paper/main.tex:832–840`. -/
theorem paired_integral_odd_kernel_quadratic {d : ℕ}
    {f k : ℝ × Vec d → ℝ} (hf : Integrable f volume)
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hodd : ∀ z, k (-z) = -k z) :
    Integrable (fun z : ℝ × Vec d => f z *
      (∫ w : ℝ × Vec d, k (z - w) * f w)) volume ∧
      (∫ z : ℝ × Vec d, f z * (∫ w : ℝ × Vec d, k (z - w) * f w)) = 0 := by
  obtain ⟨B, hB⟩ := hk.bounded_above_of_compact_support hkc
  have hint : Integrable (fun p : (ℝ × Vec d) × (ℝ × Vec d) =>
      f p.1 * (k (p.1 - p.2) * f p.2)) (volume.prod volume) := by
    have hh := (hf.mul_prod hf).bdd_mul
      ((hk.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => hB (p.1 - p.2))
    convert hh using 1
    ext p
    dsimp only [Function.comp_apply]
    ring
  have hi := hint.integral_prod_left
  simp_rw [integral_const_mul] at hi
  refine ⟨hi, ?_⟩
  have heq : (∫ z : ℝ × Vec d, f z * (∫ w : ℝ × Vec d, k (z - w) * f w)) =
      -(∫ z : ℝ × Vec d, f z * (∫ w : ℝ × Vec d, k (z - w) * f w)) := by
    calc
      _ = ∫ z : ℝ × Vec d, ∫ w : ℝ × Vec d, f z * (k (z - w) * f w) := by
        simp_rw [integral_const_mul]
      _ = ∫ z : ℝ × Vec d, ∫ w : ℝ × Vec d, f w * (k (w - z) * f z) :=
        integral_integral_swap hint
      _ = ∫ z : ℝ × Vec d, ∫ w : ℝ × Vec d, -(f z * (k (z - w) * f w)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun w => by
            have hkzw : k (w - z) = -k (z - w) := by
              rw [← neg_sub z w, hodd]
            dsimp only
            rw [hkzw]
            ring
      _ = _ := by simp_rw [integral_neg, integral_const_mul]
  linarith only [heq]

/-- The derivative of an even smooth regularization has zero self-pairing.
No strong derivative of the input field is used.
Source: `paper/main.tex:832–840`. -/
theorem paired_regularization_self_pairing_zero {d : ℕ}
    {f ρ : ℝ × Vec d → ℝ} (hf : Integrable f volume)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (heven : ∀ z, ρ (-z) = ρ z) (v : ℝ × Vec d) :
    Integrable (fun z => f z *
      fderiv ℝ (fun y => ∫ w : ℝ × Vec d, f w * ρ (y - w)) z v) volume ∧
      (∫ z, f z *
        fderiv ℝ (fun y => ∫ w : ℝ × Vec d, f w * ρ (y - w)) z v) = 0 := by
  have hc : Continuous (fun z => fderiv ℝ ρ z v) :=
    ((contDiff_infty_iff_fderiv.mp hρ).2.clm_apply contDiff_const).continuous
  have hh := paired_integral_odd_kernel_quadratic hf hc (hρc.fderiv_apply ℝ v)
    (fun z => paired_fderiv_even_kernel hρ heven z v)
  have heq : (fun z => f z *
      fderiv ℝ (fun y => ∫ w : ℝ × Vec d, f w * ρ (y - w)) z v) =
      (fun z => f z * (∫ w : ℝ × Vec d, fderiv ℝ ρ (z - w) v * f w)) := by
    funext z
    rw [paired_fderiv_regularization hf.locallyIntegrable hρ hρc]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => mul_comm _ _
  rw [heq]
  exact hh

end EinsteinRelation.Correctors
