import EinsteinRelation.Correctors.PairedPDEKernelCancellation
import EinsteinRelation.Correctors.PairedPDERegularizedTesting

/-! # Exact temporal pairing for the actual regularized energy test

Source: `paper/main.tex:832–840`. The temporal self-pairing cancels for
an even kernel. Only the derivative of the smooth outer cutoff remains.
This is an identity before taking the approximation limit.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- Temporal cancellation for the double-cutoff test of the actual weak
solution. No temporal derivative of the weak solution is assumed.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_regularized_time_pairing {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : MeasurableSet U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ ρ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (heven : ∀ z, ρ (-z) = ρ z) :
    let C := fun z : ℝ × Vec d => ∫ w : ℝ × Vec d, ζ w * u w * ρ (z - w)
    (∫ z in I ×ˢ U, u z * fderiv ℝ (fun y => ζ y * C y) z (1, 0)) =
      ∫ z in I ×ˢ U, u z * fderiv ℝ ζ z (1, 0) * C z := by
  dsimp only
  let f := fun z => ζ z * u z
  let C := fun z : ℝ × Vec d => ∫ w : ℝ × Vec d, f w * ρ (z - w)
  have hf := parabolicSolution_cutoff_memLp_global hI hU hsol hζ.continuous hζc hζsupp
  have hfi : Integrable f volume :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
      ((hf.locallyIntegrable (by norm_num)).integrableOn_isCompact hζc.mul_right)
  have hc : ContDiff ℝ (⊤ : ℕ∞) C :=
    hρc.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      hfi.locallyIntegrable hρ
  have hzero := paired_regularization_self_pairing_zero hfi hρ hρc heven (1, 0)
  have ha : Integrable (fun z => u z * (fderiv ℝ ζ z (1, 0) * C z))
      (volume.restrict (I ×ˢ U)) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ ζ z (1, 0)) :=
      (contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const
    have hm : MemLp (fun z => fderiv ℝ ζ z (1, 0) * C z) 2
        (volume.restrict (I ×ˢ U)) :=
      ((hd.mul hc).continuous.memLp_of_hasCompactSupport
        (hζc.fderiv_apply ℝ (1, 0)).mul_right).mono_measure Measure.restrict_le_self
    exact hsol.1.integrable_mul hm
  have hb := hzero.1.integrableOn (s := I ×ˢ U)
  have hzb : (∫ z in I ×ˢ U, f z * fderiv ℝ C z (1, 0)) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hzero.2
    · intro z hz
      have hn : z ∉ tsupport ζ := fun hx => hz (hζsupp hx)
      simp only [f, image_eq_zero_of_notMem_tsupport hn, zero_mul]
  change (∫ z in I ×ˢ U, u z * fderiv ℝ (fun y => ζ y * C y) z (1, 0)) =
    ∫ z in I ×ˢ U, u z * fderiv ℝ ζ z (1, 0) * C z
  calc
    _ = ∫ z in I ×ˢ U,
        u z * (fderiv ℝ ζ z (1, 0) * C z) + f z * fderiv ℝ C z (1, 0) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [fderiv_fun_mul (hζ.differentiable (by norm_cast) z)
          (hc.differentiable (by norm_cast) z)]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul, f]
        ring
    _ = (∫ z in I ×ˢ U, u z * (fderiv ℝ ζ z (1, 0) * C z)) +
        ∫ z in I ×ˢ U, f z * fderiv ℝ C z (1, 0) := integral_add ha hb
    _ = _ := by rw [hzb, add_zero]; simp only [mul_assoc, C, f]

end EinsteinRelation.Correctors
