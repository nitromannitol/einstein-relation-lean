import EinsteinRelation.Correctors.PairedPDEGradientEnergyTransfer

/-! # From compact cutoff energy to an unweighted cylinder norm

Source: `paper/main.tex:798–806,832–840`. An actual cutoff which is one
on the inner cylinder controls its unweighted gradient RMS. The comparison
retains the exact normalization of both space-time domains.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Unweighted inner energy is controlled by the actual compact-cutoff
Caccioppoli estimate, with its exact volume ratio.
Source: `paper/main.tex:798–806,832–840`. -/
theorem parabolicSolution_inner_rms_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    {V : Set (ℝ × Vec d)} (hV : MeasurableSet V) (hVsub : V ⊆ I ×ˢ U)
    (hV0 : volume V ≠ 0) (hVfin : volume V ≠ ∞)
    (hDfin : volume (I ×ˢ U) ≠ ∞)
    (hζ1 : ∀ z ∈ V, ζ z = 1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z ∈ I ×ˢ U, 2*ζ z*fderiv ℝ ζ z (1,0) +
      4*K^2*euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) ≤ B) :
    vectorRms volume V G ≤
      Real.sqrt (B * volume.real (I ×ˢ U) / volume.real V) *
        scalarRms volume (I ×ˢ U) u := by
  let D := I ×ˢ U
  letI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDfin
  have hD0 : volume D ≠ 0 := ne_zero_of_lt
    ((pos_iff_ne_zero.mpr hV0).trans_le (measure_mono hVsub))
  have hVr : 0 < volume.real V := ENNReal.toReal_pos hV0 hVfin
  have hDr : 0 < volume.real D := ENNReal.toReal_pos hD0 hDfin
  have henergy := parabolicSolution_cutoff_energy hK hI hU hsol hζ hζc hζsupp
  have hsq (z : ℝ × Vec d) : 0 ≤ euclideanSq (G z) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hinner : (∫ z in V, euclideanSq (G z)) ≤
      ∫ z in D, ζ z^2*euclideanSq (G z) := by
    calc
      _ = ∫ z in V, ζ z^2*euclideanSq (G z) :=
        setIntegral_congr_fun hV (fun z hz => by rw [hζ1 z hz, one_pow, one_mul])
      _ ≤ _ := setIntegral_mono_set henergy.1
        (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hsq z)) hVsub.eventuallyLE
  have hle := hinner.trans (parabolicSolution_cutoff_energy_le_scalar
    hK hI hU hsol hζ hζc hζsupp hB)
  have hid : volume.real D * (⨍ z in D, u z^2) = ∫ z in D, u z^2 := by
    simpa only [measureReal_restrict_apply_univ, smul_eq_mul] using
      (measure_smul_average (μ := volume.restrict D) (fun z => u z^2))
  have hle' := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hVr.le))
  change Real.sqrt (⨍ z in V, euclideanSq (G z)) ≤ _
  simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul] at hle' ⊢
  rw [← hid, show (volume.real V)⁻¹ * (B*(volume.real D * (⨍ z in D, u z^2))) =
      (B*volume.real D / volume.real V) * (⨍ z in D, u z^2) by ring,
    Real.sqrt_mul (div_nonneg (mul_nonneg hB0 hDr.le) hVr.le)] at hle'
  exact hle'

end EinsteinRelation.Correctors
