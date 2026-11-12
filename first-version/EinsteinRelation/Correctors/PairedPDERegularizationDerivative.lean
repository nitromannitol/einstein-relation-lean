import EinsteinRelation.Correctors.PairedPDESmoothRegularization
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Derivatives of actual compact regularizations

Source: `paper/main.tex:832–840`. The derivative acts on the smooth kernel,
not on the weak solution. Even kernels have odd directional derivatives.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Differentiate a compact smooth convolution in any space-time direction.
The input field needs only local integrability.
Source: `paper/main.tex:832–840`. -/
theorem paired_fderiv_regularization {d : ℕ}
    {f ρ : ℝ × Vec d → ℝ} (hf : LocallyIntegrable f volume)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (z v : ℝ × Vec d) :
    fderiv ℝ (fun y => ∫ w : ℝ × Vec d, f w * ρ (y - w)) z v =
      ∫ w : ℝ × Vec d, f w * fderiv ℝ ρ (z - w) v := by
  letI : (volume : Measure (ℝ × Vec d)).IsAddLeftInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddLeftInvariant
    infer_instance
  let L := ContinuousLinearMap.mul ℝ ℝ
  have h1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_cast)
  have hd := hρc.hasFDerivAt_convolution_right (L := L) hf h1 z
  change (fderiv ℝ (convolution f ρ L volume) z) v = _
  rw [hd.fderiv]
  exact convolution_precompR_apply (L := L) hf (hρc.fderiv ℝ)
    (contDiff_infty_iff_fderiv.mp hρ).2.continuous z v

/-- An even smooth kernel has odd derivatives, including the temporal
derivative used in the energy test. Source: `paper/main.tex:832–840`. -/
theorem paired_fderiv_even_kernel {d : ℕ} {ρ : ℝ × Vec d → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (heven : ∀ z, ρ (-z) = ρ z)
    (z v : ℝ × Vec d) :
    fderiv ℝ ρ (-z) v = -fderiv ℝ ρ z v := by
  have hdiff : Differentiable ℝ ρ := hρ.differentiable (by norm_cast)
  have hd := (hdiff (-z)).hasFDerivAt.comp z (hasFDerivAt_id z).neg
  have heq : (fun y => ρ (-y)) = ρ := funext heven
  change HasFDerivAt (fun y => ρ (-y)) _ z at hd
  rw [heq] at hd
  have hlin := hd.unique (hdiff z).hasFDerivAt
  have hv := congrArg (fun L : (ℝ × Vec d) →L[ℝ] ℝ => L v) hlin
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg] at hv
  linarith only [hv]

end EinsteinRelation.Correctors
