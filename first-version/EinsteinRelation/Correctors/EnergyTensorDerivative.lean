import EinsteinRelation.Correctors.PairedPDETesting

namespace EinsteinRelation.Correctors
/-- Derivative of a tensor cutoff, used in weak energy testing;
source `paper/main.tex:824–832`. -/
theorem fderiv_energy_tensor {d : ℕ} {η : ℝ → ℝ} {ψ : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z v : ℝ × Vec d) :
    fderiv ℝ (fun w : ℝ × Vec d => η w.1 * ψ w.2) z v =
      deriv η z.1 * v.1 * ψ z.2 + η z.1 * fderiv ℝ ψ z.2 v.2 := by
  have hηd := (hη.differentiable (by norm_num)).differentiableAt (x := z.1)
  have hψd := (hψ.differentiable (by norm_num)).differentiableAt (x := z.2)
  have hf : DifferentiableAt ℝ (fun w : ℝ × Vec d => η w.1) z :=
    hηd.comp z differentiableAt_fst
  have hg : DifferentiableAt ℝ (fun w : ℝ × Vec d => ψ w.2) z :=
    hψd.comp z differentiableAt_snd
  change fderiv ℝ ((fun w : ℝ × Vec d => η w.1) * (fun w => ψ w.2)) z v = _
  have he : fderiv ℝ (fun w : ℝ × Vec d => η w.1) z =
      (fderiv ℝ η z.1).comp (fderiv ℝ Prod.fst z) :=
    fderiv_comp z hηd differentiableAt_fst
  have hp : fderiv ℝ (fun w : ℝ × Vec d => ψ w.2) z =
      (fderiv ℝ ψ z.2).comp (fderiv ℝ Prod.snd z) :=
    fderiv_comp z hψd differentiableAt_snd
  rw [fderiv_mul hf hg, he, hp]
  simp [fderiv_fst, fderiv_snd]
  ring
end EinsteinRelation.Correctors
