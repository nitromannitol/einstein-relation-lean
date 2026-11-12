import EinsteinRelation.Correctors.ParabolicFluxSolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Exact derivatives of a smooth tensor cutoff.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem parabolic_tensor_cutoff_derivative {d : ℕ} {η : ℝ → ℝ} {χ : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (z w : ℝ × Vec d) :
    fderiv ℝ (fun z : ℝ × Vec d => η z.1 * χ z.2) z w =
      deriv η z.1 * w.1 * χ z.2 + η z.1 * fderiv ℝ χ z.2 w.2 := by
  have hηd := (hη.differentiable (by norm_num)).differentiableAt (x := z.1)
  have hχd := (hχ.differentiable (by norm_num)).differentiableAt (x := z.2)
  have hf : DifferentiableAt ℝ (fun w : ℝ × Vec d => η w.1) z :=
    hηd.comp z differentiableAt_fst
  have hg : DifferentiableAt ℝ (fun w : ℝ × Vec d => χ w.2) z :=
    hχd.comp z differentiableAt_snd
  change fderiv ℝ ((fun w : ℝ × Vec d => η w.1) * (fun w => χ w.2)) z w = _
  have he : fderiv ℝ (fun w : ℝ × Vec d => η w.1) z =
      (fderiv ℝ η z.1).comp (fderiv ℝ Prod.fst z) :=
    fderiv_comp z hηd differentiableAt_fst
  have hp : fderiv ℝ (fun w : ℝ × Vec d => χ w.2) z =
      (fderiv ℝ χ z.2).comp (fderiv ℝ Prod.snd z) :=
    fderiv_comp z hχd differentiableAt_snd
  rw [fderiv_mul hf hg, he, hp]
  simp [fderiv_fst, fderiv_snd]
  ring

end EinsteinRelation.Correctors
