import EinsteinRelation.Correctors.PairedPDERegularizationDerivative

/-! # Regularizing the actual spatial weak derivative

Source: `paper/main.tex:832–840`. Testing the global weak derivative
against a translated reflected kernel moves spatial differentiation from
the kernel to the energy-class field.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Convolution commutes with an actual spatial weak derivative.
Source: `paper/main.tex:832–840`. -/
theorem paired_fderiv_convolution_of_spatial_weak_derivative {d : ℕ}
    {u g : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume)
    (j : Fin d)
    (hweak : ∀ (φ : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      (∫ z : ℝ × Vec d, u z * fderiv ℝ φ z (0, unitVector j)) =
        -(∫ z : ℝ × Vec d, g z * φ z))
    {ρ : ℝ × Vec d → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (z : ℝ × Vec d) :
    fderiv ℝ (fun y : ℝ × Vec d => ∫ w : ℝ × Vec d, ρ (y - w) * u w)
      z (0, unitVector j) =
        ∫ w : ℝ × Vec d, ρ (z - w) * g w := by
  have heq : (fun y : ℝ × Vec d => ∫ w : ℝ × Vec d, ρ (y - w) * u w) =
      (fun y : ℝ × Vec d => ∫ w : ℝ × Vec d, u w * ρ (y - w)) := by
    funext y
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => mul_comm _ _
  rw [heq, paired_fderiv_regularization (hu.locallyIntegrable (by norm_num)) hρ hρc]
  let φ : ℝ × Vec d → ℝ := fun w => ρ (z - w)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hρ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := hρc.comp_homeomorph (Homeomorph.subLeft z)
  have hd (w : ℝ × Vec d) : fderiv ℝ φ w (0, unitVector j) =
      -fderiv ℝ ρ (z - w) (0, unitVector j) := by
    have hsub := (hasFDerivAt_const (𝕜 := ℝ) z w).sub (hasFDerivAt_id w)
    have hp := (hρ.differentiable (by norm_cast) (z - w)).hasFDerivAt.comp w hsub
    change HasFDerivAt φ _ w at hp
    rw [hp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, zero_sub, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg]
  have ht := hweak φ hφ hφc
  simp_rw [hd, mul_neg] at ht
  rw [integral_neg] at ht
  have hh := neg_injective ht
  exact hh.trans (integral_congr_ae (Filter.Eventually.of_forall fun w => mul_comm _ _))

end EinsteinRelation.Correctors
