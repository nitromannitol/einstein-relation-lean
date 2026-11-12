import EinsteinRelation.Correctors.PairedCorrectorPlanarAmplitude
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
/-- The two centered amplitude seminorms have one energy bound; source
`paper/main.tex:872–883`. -/
theorem paired_planar_joint_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (f h E : Ω → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hE : MemLp E p μ)
    (hdom : ∀ᵐ ω ∂μ, |f ω| + |h ω| ≤ K * E ω) :
    MemLp f p μ ∧ MemLp h p μ ∧
      eLpNorm f p μ + eLpNorm h p μ ≤
        ENNReal.ofReal (2*K) * eLpNorm E p μ := by
  -- Bound for f: |f ω| ≤ K * |E ω| almost everywhere
  have h_f_bound_abs : ∀ᵐ ω ∂μ, |f ω| ≤ K * |E ω| := by
    filter_upwards [hdom] with ω hω
    by_cases hE_nonneg : 0 ≤ E ω
    · rw [abs_of_nonneg hE_nonneg]
      exact le_trans (le_add_of_nonneg_right (abs_nonneg _)) hω
    · -- E ω < 0, so K * E ω ≤ 0, forcing |f ω| = 0
      have hK_mul_E_nonpos : K * E ω ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hK (le_of_lt (not_le.mp hE_nonneg))
      have hf_abs_le : |f ω| ≤ K * E ω :=
        le_trans (le_add_of_nonneg_right (abs_nonneg _)) hω
      have hf_abs_zero : |f ω| = 0 := by
        have h_nonneg : 0 ≤ |f ω| := abs_nonneg _
        linarith
      rw [hf_abs_zero]
      exact mul_nonneg hK (abs_nonneg _)
  -- Bound for h: |h ω| ≤ K * |E ω| almost everywhere
  have h_h_bound_abs : ∀ᵐ ω ∂μ, |h ω| ≤ K * |E ω| := by
    filter_upwards [hdom] with ω hω
    by_cases hE_nonneg : 0 ≤ E ω
    · rw [abs_of_nonneg hE_nonneg]
      exact le_trans (le_add_of_nonneg_left (abs_nonneg _)) hω
    · -- E ω < 0, so K * E ω ≤ 0, forcing |h ω| = 0
      have hK_mul_E_nonpos : K * E ω ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hK (le_of_lt (not_le.mp hE_nonneg))
      have hh_abs_le : |h ω| ≤ K * E ω :=
        le_trans (le_add_of_nonneg_left (abs_nonneg _)) hω
      have hh_abs_zero : |h ω| = 0 := by
        have h_nonneg : 0 ≤ |h ω| := abs_nonneg _
        linarith
      rw [hh_abs_zero]
      exact mul_nonneg hK (abs_nonneg _)
  -- eLpNorm bounds using the standard lemma
  have h_eLpNorm_f : eLpNorm f p μ ≤ ENNReal.ofReal K * eLpNorm E p μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by
      filter_upwards [h_f_bound_abs] with ω hω
      simpa [Real.norm_eq_abs] using hω
    ) p
  have h_eLpNorm_h : eLpNorm h p μ ≤ ENNReal.ofReal K * eLpNorm E p μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by
      filter_upwards [h_h_bound_abs] with ω hω
      simpa [Real.norm_eq_abs] using hω
    ) p
  -- MemLp bounds using MemLp.mono'
  have hE_mul_K : MemLp (fun ω => K * E ω) p μ := hE.const_mul K
  have hf_mem : MemLp f p μ := hE_mul_K.mono' hf (by
    filter_upwards [hdom] with ω hω
    simpa [Real.norm_eq_abs] using le_trans (le_add_of_nonneg_right (abs_nonneg _)) hω)
  have hh_mem : MemLp h p μ := hE_mul_K.mono' hh (by
    filter_upwards [hdom] with ω hω
    simpa [Real.norm_eq_abs] using le_trans (le_add_of_nonneg_left (abs_nonneg _)) hω)
  -- Combine the eLpNorm bounds
  have h_sum : eLpNorm f p μ + eLpNorm h p μ ≤ ENNReal.ofReal (2*K) * eLpNorm E p μ := by
    calc
      eLpNorm f p μ + eLpNorm h p μ ≤
          (ENNReal.ofReal K * eLpNorm E p μ) + (ENNReal.ofReal K * eLpNorm E p μ) := by gcongr
      _ = (ENNReal.ofReal K + ENNReal.ofReal K) * eLpNorm E p μ := by ring
      _ = ENNReal.ofReal (K + K) * eLpNorm E p μ := by rw [ENNReal.ofReal_add hK hK]
      _ = ENNReal.ofReal (2*K) * eLpNorm E p μ := by rw [two_mul]
  exact ⟨hf_mem, hh_mem, h_sum⟩
end EinsteinRelation.Correctors
