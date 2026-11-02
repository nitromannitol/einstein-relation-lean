import EinsteinRelation.Entropy.DivergenceSecondAssertion
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors
/-- Continuity of two varying L² factors, for regularized energy pairings.
Source: `paper/main.tex:822–830`. -/
theorem paired_tendsto_integral_mul_L2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} {fseq gseq : ℕ → X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfs : ∀ k, MemLp (fseq k) 2 μ) (hgs : ∀ k, MemLp (gseq k) 2 μ)
    (hflim : Tendsto (fun k => eLpNorm (fun x => fseq k x - f x) 2 μ) atTop (𝓝 0))
    (hglim : Tendsto (fun k => eLpNorm (fun x => gseq k x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, fseq k x * gseq k x ∂μ) atTop
      (𝓝 (∫ x, f x * g x ∂μ)) := by
  have hdiff : ∀ k, ∫ x, fseq k x * gseq k x ∂μ - ∫ x, f x * g x ∂μ =
      ∫ x, (fseq k x - f x) * (gseq k x - g x) ∂μ +
      ∫ x, (fseq k x - f x) * g x ∂μ +
      ∫ x, f x * (gseq k x - g x) ∂μ := by
    intro k
    have hi1 : Integrable (fun x => fseq k x * gseq k x) μ := (hfs k).integrable_mul (hgs k)
    have hi2 : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
    have hi3 : Integrable (fun x => (fseq k x - f x) * (gseq k x - g x)) μ :=
      ((hfs k).sub hf).integrable_mul ((hgs k).sub hg)
    have hi4 : Integrable (fun x => (fseq k x - f x) * g x) μ :=
      ((hfs k).sub hf).integrable_mul hg
    have hi5 : Integrable (fun x => f x * (gseq k x - g x)) μ := hf.integrable_mul ((hgs k).sub hg)
    calc
      ∫ x, fseq k x * gseq k x ∂μ - ∫ x, f x * g x ∂μ =
          ∫ x, (fseq k x * gseq k x - f x * g x) ∂μ := by
        rw [integral_sub hi1 hi2]
      _ = ∫ x, ((fseq k x - f x) * (gseq k x - g x) +
          (fseq k x - f x) * g x + f x * (gseq k x - g x)) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        ring
      _ = ∫ x, (((fseq k x - f x) * (gseq k x - g x) + (fseq k x - f x) * g x) +
          f x * (gseq k x - g x)) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        ring
      _ = (∫ x, ((fseq k x - f x) * (gseq k x - g x) + (fseq k x - f x) * g x) ∂μ) +
          ∫ x, f x * (gseq k x - g x) ∂μ := by
        simpa using integral_add (hi3.add hi4) hi5
      _ = (∫ x, (fseq k x - f x) * (gseq k x - g x) ∂μ +
          ∫ x, (fseq k x - f x) * g x ∂μ) +
          ∫ x, f x * (gseq k x - g x) ∂μ := by
        rw [integral_add hi3 hi4]
      _ = ∫ x, (fseq k x - f x) * (gseq k x - g x) ∂μ +
          ∫ x, (fseq k x - f x) * g x ∂μ +
          ∫ x, f x * (gseq k x - g x) ∂μ := by ring
  have hbound : ∀ k, ENNReal.ofReal |∫ x, fseq k x * gseq k x ∂μ - ∫ x, f x * g x ∂μ| ≤
      eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ +
      eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm g 2 μ +
      eLpNorm f 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ := by
    intro k
    have hi1 : Integrable (fun x => fseq k x * gseq k x) μ := (hfs k).integrable_mul (hgs k)
    have hi2 : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
    have hi3 : Integrable (fun x => (fseq k x - f x) * (gseq k x - g x)) μ :=
      ((hfs k).sub hf).integrable_mul ((hgs k).sub hg)
    have hi4 : Integrable (fun x => (fseq k x - f x) * g x) μ :=
      ((hfs k).sub hf).integrable_mul hg
    have hi5 : Integrable (fun x => f x * (gseq k x - g x)) μ := hf.integrable_mul ((hgs k).sub hg)
    have hm3 : AEMeasurable (fun x => ‖(fseq k x - f x) * (gseq k x - g x)‖ₑ) μ :=
      hi3.aemeasurable.enorm
    have hm4 : AEMeasurable (fun x => ‖(fseq k x - f x) * g x‖ₑ) μ :=
      hi4.aemeasurable.enorm
    have hsub_eq : (∫ x, fseq k x * gseq k x ∂μ - ∫ x, f x * g x ∂μ) =
        ∫ x, (fseq k x * gseq k x - f x * g x) ∂μ := by
      rw [integral_sub hi1 hi2]
    have h_enorm : ‖∫ x, (fseq k x * gseq k x - f x * g x) ∂μ‖ₑ ≤
        ∫⁻ x, ‖(fseq k x * gseq k x - f x * g x)‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm _
    have h_enorm' : ENNReal.ofReal |∫ x, fseq k x * gseq k x ∂μ - ∫ x, f x * g x ∂μ| ≤
        ∫⁻ x, ‖(fseq k x * gseq k x - f x * g x)‖ₑ ∂μ := by
      rw [hsub_eq]
      simpa [Real.enorm_eq_ofReal_abs] using h_enorm
    have h_tri : ∫⁻ x, ‖(fseq k x * gseq k x - f x * g x)‖ₑ ∂μ ≤
        ∫⁻ x, (‖(fseq k x - f x) * (gseq k x - g x)‖ₑ +
          ‖(fseq k x - f x) * g x‖ₑ + ‖f x * (gseq k x - g x)‖ₑ) ∂μ := by
      refine lintegral_mono fun x => ?_
      have h_eq : (fseq k x * gseq k x - f x * g x) =
          (fseq k x - f x) * (gseq k x - g x) + (fseq k x - f x) * g x + f x * (gseq k x - g x) := by
        ring
      rw [h_eq]
      have h1 : ‖(fseq k x - f x) * (gseq k x - g x) + (fseq k x - f x) * g x + f x * (gseq k x - g x)‖ₑ
          ≤ ‖(fseq k x - f x) * (gseq k x - g x) + (fseq k x - f x) * g x‖ₑ +
            ‖f x * (gseq k x - g x)‖ₑ := enorm_add_le _ _
      have h2 : ‖(fseq k x - f x) * (gseq k x - g x) + (fseq k x - f x) * g x‖ₑ +
          ‖f x * (gseq k x - g x)‖ₑ ≤
          (‖(fseq k x - f x) * (gseq k x - g x)‖ₑ + ‖(fseq k x - f x) * g x‖ₑ) +
          ‖f x * (gseq k x - g x)‖ₑ := add_le_add (enorm_add_le _ _) (le_refl _)
      have h3 : (‖(fseq k x - f x) * (gseq k x - g x)‖ₑ + ‖(fseq k x - f x) * g x‖ₑ) +
          ‖f x * (gseq k x - g x)‖ₑ =
          ‖(fseq k x - f x) * (gseq k x - g x)‖ₑ +
          ‖(fseq k x - f x) * g x‖ₑ + ‖f x * (gseq k x - g x)‖ₑ := by ring
      exact h1.trans (h2.trans h3.le)
    have h_split : ∫⁻ x, (‖(fseq k x - f x) * (gseq k x - g x)‖ₑ +
        ‖(fseq k x - f x) * g x‖ₑ + ‖f x * (gseq k x - g x)‖ₑ) ∂μ =
        (∫⁻ x, ‖(fseq k x - f x) * (gseq k x - g x)‖ₑ ∂μ +
          ∫⁻ x, ‖(fseq k x - f x) * g x‖ₑ ∂μ) +
        ∫⁻ x, ‖f x * (gseq k x - g x)‖ₑ ∂μ := by
      have hmAB : AEMeasurable (fun x => ‖(fseq k x - f x) * (gseq k x - g x)‖ₑ +
        ‖(fseq k x - f x) * g x‖ₑ) μ := hm3.add hm4
      calc
        ∫⁻ x, (‖(fseq k x - f x) * (gseq k x - g x)‖ₑ +
          ‖(fseq k x - f x) * g x‖ₑ + ‖f x * (gseq k x - g x)‖ₑ) ∂μ
            = (∫⁻ x, (‖(fseq k x - f x) * (gseq k x - g x)‖ₑ +
              ‖(fseq k x - f x) * g x‖ₑ) ∂μ) + ∫⁻ x, ‖f x * (gseq k x - g x)‖ₑ ∂μ := by
          rw [lintegral_add_left' hmAB (fun x => ‖f x * (gseq k x - g x)‖ₑ)]
        _ = ((∫⁻ x, ‖(fseq k x - f x) * (gseq k x - g x)‖ₑ ∂μ) +
          ∫⁻ x, ‖(fseq k x - f x) * g x‖ₑ ∂μ) + ∫⁻ x, ‖f x * (gseq k x - g x)‖ₑ ∂μ := by
          rw [lintegral_add_left' hm3 (fun x => ‖(fseq k x - f x) * g x‖ₑ)]
        _ = (∫⁻ x, ‖(fseq k x - f x) * (gseq k x - g x)‖ₑ ∂μ +
          ∫⁻ x, ‖(fseq k x - f x) * g x‖ₑ ∂μ) + ∫⁻ x, ‖f x * (gseq k x - g x)‖ₑ ∂μ := rfl
    have h_lintegral_eq : (∫⁻ x, ‖(fseq k x - f x) * (gseq k x - g x)‖ₑ ∂μ +
        ∫⁻ x, ‖(fseq k x - f x) * g x‖ₑ ∂μ) +
        ∫⁻ x, ‖f x * (gseq k x - g x)‖ₑ ∂μ =
        eLpNorm (fun x => (fseq k x - f x) * (gseq k x - g x)) 1 μ +
        eLpNorm (fun x => (fseq k x - f x) * g x) 1 μ +
        eLpNorm (fun x => f x * (gseq k x - g x)) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm hi3.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm hi4.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm hi5.aestronglyMeasurable]
    have h_cauchy_schwarz : eLpNorm (fun x => (fseq k x - f x) * (gseq k x - g x)) 1 μ +
        eLpNorm (fun x => (fseq k x - f x) * g x) 1 μ +
        eLpNorm (fun x => f x * (gseq k x - g x)) 1 μ ≤
        eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ +
        eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm g 2 μ +
        eLpNorm f 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ := by
      have h1 : eLpNorm (fun x => (fseq k x - f x) * (gseq k x - g x)) 1 μ ≤
          eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ := by
        have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
          ((hfs k).aestronglyMeasurable.sub hf.aestronglyMeasurable) ((hgs k).aestronglyMeasurable.sub hg.aestronglyMeasurable)
        simpa [smul_eq_mul, Pi.mul_apply, mul_comm] using! this
      have h2 : eLpNorm (fun x => (fseq k x - f x) * g x) 1 μ ≤
          eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm g 2 μ := by
        have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
          ((hfs k).aestronglyMeasurable.sub hf.aestronglyMeasurable) hg.aestronglyMeasurable
        simpa [smul_eq_mul, Pi.mul_apply, mul_comm] using! this
      have h3 : eLpNorm (fun x => f x * (gseq k x - g x)) 1 μ ≤
          eLpNorm f 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ := by
        have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
          hf.aestronglyMeasurable ((hgs k).aestronglyMeasurable.sub hg.aestronglyMeasurable)
        simpa [smul_eq_mul, Pi.mul_apply, mul_comm] using! this
      have hsum12 : eLpNorm (fun x => (fseq k x - f x) * (gseq k x - g x)) 1 μ +
          eLpNorm (fun x => (fseq k x - f x) * g x) 1 μ ≤
          eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ +
          eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm g 2 μ :=
        add_le_add h1 h2
      have hsum : (eLpNorm (fun x => (fseq k x - f x) * (gseq k x - g x)) 1 μ +
          eLpNorm (fun x => (fseq k x - f x) * g x) 1 μ) +
          eLpNorm (fun x => f x * (gseq k x - g x)) 1 μ ≤
          (eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ +
          eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm g 2 μ) +
          eLpNorm f 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ :=
        add_le_add hsum12 h3
      simpa [add_assoc] using hsum
    calc
      ENNReal.ofReal |∫ x, fseq k x * gseq k x ∂μ - ∫ x, f x * g x ∂μ| ≤
          ∫⁻ x, ‖(fseq k x * gseq k x - f x * g x)‖ₑ ∂μ := h_enorm'
      _ ≤ ∫⁻ x, (‖(fseq k x - f x) * (gseq k x - g x)‖ₑ +
          ‖(fseq k x - f x) * g x‖ₑ + ‖f x * (gseq k x - g x)‖ₑ) ∂μ := h_tri
      _ = (∫⁻ x, ‖(fseq k x - f x) * (gseq k x - g x)‖ₑ ∂μ +
          ∫⁻ x, ‖(fseq k x - f x) * g x‖ₑ ∂μ) +
          ∫⁻ x, ‖f x * (gseq k x - g x)‖ₑ ∂μ := h_split
      _ = eLpNorm (fun x => (fseq k x - f x) * (gseq k x - g x)) 1 μ +
          eLpNorm (fun x => (fseq k x - f x) * g x) 1 μ +
          eLpNorm (fun x => f x * (gseq k x - g x)) 1 μ := h_lintegral_eq
      _ ≤ eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ +
          eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm g 2 μ +
          eLpNorm f 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ := h_cauchy_schwarz
  have hTendsto : Tendsto (fun k : ℕ =>
      eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ +
      eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm g 2 μ +
      eLpNorm f 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ) atTop (𝓝 0) := by
    have h12 : Tendsto (fun k => eLpNorm (fun x => fseq k x - f x) 2 μ *
        eLpNorm (fun x => gseq k x - g x) 2 μ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul hflim (Or.inr ENNReal.zero_ne_top) hglim (Or.inr ENNReal.zero_ne_top)
      simpa [mul_zero] using! this
    have h13 : Tendsto (fun k => eLpNorm (fun x => fseq k x - f x) 2 μ * eLpNorm g 2 μ)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const hflim (Or.inr hg.eLpNorm_ne_top)
      simpa [mul_zero] using! this
    have h23 : Tendsto (fun k => eLpNorm f 2 μ * eLpNorm (fun x => gseq k x - g x) 2 μ)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hglim (Or.inr hf.eLpNorm_ne_top)
      simpa [mul_zero] using! this
    have hsum12_13 := h12.add h13
    have hsum := hsum12_13.add h23
    simpa [add_assoc] using hsum
  have hT : Tendsto (fun k => ∫ x, fseq k x * gseq k x ∂μ - ∫ x, f x * g x ∂μ) atTop (𝓝 0) :=
    EinsteinRelation.Entropy.tendsto_zero_of_ofReal_abs_le' hTendsto hbound
  rw [← tendsto_sub_nhds_zero_iff]
  simpa [hdiff] using hT
end EinsteinRelation.Correctors
