import EinsteinRelation.Correctors.AKMHeatKernelCutoffLocalization
import EinsteinRelation.Correctors.PairedPDEGradientEnergyTransfer

/-! # Whole-space cutoff energy from local Caccioppoli

Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof.
Compact spatial tests allow the proved local energy inequality to be
used on a whole-space strip without assuming global gradient energy.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A plateau in time converts compact Caccioppoli into a uniform bound
for the spatially cut off gradient on a smaller strip.
Source: `paper/main.tex:787–792,850`. -/
theorem parabolic_global_cutoff_energy {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hJI : J ⊆ I) {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : ∀ R : ℝ, 0 < R → IsParabolicSolution A I (originBall d R) u G)
    (hu : MemLp u 2 (volume.restrict (I ×ˢ Set.univ)))
    {η : ℝ → ℝ} {χ : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ interior I) (hηone : ∀ t ∈ J, η t = 1)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : let ζ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2
      ∀ z ∈ I ×ˢ (Set.univ : Set (Vec d)),
        2 * ζ z * fderiv ℝ ζ z (1,0) +
          4 * K^2 * euclideanSq (fun j => fderiv ℝ ζ z (0,unitVector j)) ≤ B) :
    Integrable (fun z => χ z.2 ^ 2 * euclideanSq (G z))
      (volume.restrict (J ×ˢ Set.univ)) ∧
    (∫ z in J ×ˢ Set.univ, χ z.2 ^ 2 * euclideanSq (G z)) ≤
      B * ∫ z in I ×ˢ Set.univ, u z ^ 2 := by
  obtain ⟨n, hn⟩ := akm_compact_subset_originBall hχc
  have hR : 0 < (n+1 : ℝ) := by positivity
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).norm
  have hU : IsOpen (originBall d (n+1)) := isOpen_lt hnorm continuous_const
  let ζ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ :=
    (hη.comp contDiff_fst).mul (hχ.comp contDiff_snd)
  have hζc : HasCompactSupport ζ := by
    simpa only [pow_one, mul_one] using
      hasCompactSupport_tensor_cutoff hηc hχc 1 (by decide) (fun _ => (1 : ℝ))
  have hζs : tsupport ζ ⊆ interior I ×ˢ originBall d (n+1) := by
    apply Set.Subset.trans ?_ (Set.prod_mono hηs hn)
    apply closure_minimal ?_ ((isClosed_tsupport η).prod (isClosed_tsupport χ))
    intro z hz
    exact ⟨subset_tsupport η (fun he => hz (by simp only [ζ, he, zero_mul])),
      subset_tsupport χ (fun he => hz (by simp only [ζ, he, mul_zero]))⟩
  let f : ℝ × Vec d → ℝ := fun z => ζ z ^ 2 * euclideanSq (G z)
  have hlocal := parabolicSolution_cutoff_energy hK hI hU
    (hsol (n+1) hR) hζ hζc hζs
  have hf : Integrable f volume := by
    apply (integrableOn_iff_integrable_of_support_subset (s := I ×ˢ originBall d (n+1)) ?_).mp hlocal.1
    intro z hz
    have hzz : ζ z ≠ 0 := fun he => hz (by simp only [he, zero_pow (by decide : 2 ≠ 0), zero_mul])
    exact ⟨interior_subset (hζs (subset_tsupport ζ hzz)).1,
      (hζs (subset_tsupport ζ hzz)).2⟩
  have heq : (fun z => χ z.2 ^ 2 * euclideanSq (G z)) =ᵐ[volume.restrict (J ×ˢ Set.univ)] f := by
    filter_upwards [ae_restrict_mem (hJ.prod MeasurableSet.univ)] with z hz
    simp only [f, ζ, hηone z.1 hz.1, one_mul]
  refine ⟨(hf.integrableOn).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  calc
    (∫ z in J ×ˢ Set.univ, f z) ≤ ∫ z in I ×ˢ Set.univ, f z :=
      setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall (fun z =>
        mul_nonneg (sq_nonneg _) (euclideanSq_nonneg_fisher _)))
        (Filter.Eventually.of_forall (fun z hz => ⟨hJI hz.1, hz.2⟩))
    _ = ∫ z in I ×ˢ originBall d (n+1), f z :=
      akm_spatially_supported_strip_integral hI hn (fun z hz => by
        simp only [f, ζ, hz, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_mul])
    _ ≤ B * ∫ z in I ×ˢ originBall d (n+1), u z ^ 2 :=
      parabolicSolution_cutoff_energy_le_scalar hK hI hU
        (hsol (n+1) hR) hζ hζc hζs (fun z hz => hB z ⟨hz.1, Set.mem_univ _⟩)
    _ ≤ B * ∫ z in I ×ˢ Set.univ, u z ^ 2 := by
      apply mul_le_mul_of_nonneg_left ?_ hB0
      exact setIntegral_mono_set hu.integrable_sq
        (Filter.Eventually.of_forall (fun z => sq_nonneg (u z)))
        (Filter.Eventually.of_forall (fun z hz => ⟨hz.1, Set.mem_univ _⟩))

end EinsteinRelation.Correctors
