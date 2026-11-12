import EinsteinRelation.Correctors.PairedPDEGradientEnergyTransfer
import EinsteinRelation.Correctors.ScalarSetAverageMoments

/-! # Probability moments of the actual cutoff gradient energy

Source: `paper/main.tex:844–855`. The weak PDE and scalar pointwise moments
control the true weighted gradient energy on a finite space-time cylinder.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Scalar probability moments transfer to the actual cutoff gradient
energy. The derivative bound is deterministic and the PDE is the production
weak equation. Source: `paper/main.tex:844–855`. -/
theorem parabolicSolution_cutoff_gradient_moments {d : ℕ} {K : ℝ}
    (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A : Ω → Coefficient d K) (u : Ω → ℝ × Vec d → ℝ)
    (G : Ω → ℝ × Vec d → Vec d)
    (hum : Measurable (fun z : Ω × (ℝ × Vec d) => u z.1 z.2))
    (hGm : Measurable (fun z : Ω × (ℝ × Vec d) => G z.1 z.2))
    {I : Set ℝ} {U : Set (Vec d)} (hI : MeasurableSet I) (hU : IsOpen U)
    (hD0 : volume (I ×ˢ U) ≠ 0) (hDfin : volume (I ×ˢ U) ≠ ∞)
    (hsol : ∀ᵐ ω ∂Q, IsParabolicSolution (A ω) I U (u ω) (G ω))
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z ∈ I ×ˢ U, 2 * ζ z * fderiv ℝ ζ z (1, 0) +
      4 * K^2 * euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) ≤ B)
    {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C)
    (hmom : ∀ z ∈ I ×ˢ U, MemLp (fun ω => u ω z) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => u ω z) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    MemLp (fun ω => Real.sqrt (∫ z in I ×ˢ U, ζ z^2 * euclideanSq (G ω z)))
      (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => Real.sqrt (∫ z in I ×ˢ U, ζ z^2 * euclideanSq (G ω z)))
        (ENNReal.ofReal p) Q ≤
          ENNReal.ofReal (Real.sqrt (B * volume.real (I ×ˢ U)) * C) := by
  let D := I ×ˢ U
  let E := fun ω => Real.sqrt (∫ z in D, ζ z^2 * euclideanSq (G ω z))
  let S := fun ω => Real.sqrt (⨍ z in D, (u ω z)^2)
  let F := Real.sqrt (B * volume.real D)
  letI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDfin
  have hm := scalarL2_setAverage_moment_le Q volume (hI.prod hU.measurableSet)
    hD0 hDfin hp hC (fun z => u z.1 z.2) hum hmom
  have heq (ω : Ω) : volume.real D * (⨍ z in D, (u ω z)^2) =
      ∫ z in D, (u ω z)^2 := by
    simpa only [measureReal_restrict_apply_univ, smul_eq_mul] using
      (measure_smul_average (μ := volume.restrict D) (fun z => (u ω z)^2))
  have hEm : Measurable E := by
    have hgm : Measurable (fun z : Ω × (ℝ × Vec d) => euclideanSq (G z.1 z.2)) := by
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hGm).mul ((measurable_pi_apply j).comp hGm)
    have hj := ((hζ.continuous.measurable.comp measurable_snd).pow_const 2).mul hgm
    exact (hj.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict D)).measurable.sqrt
  have hdom : ∀ᵐ ω ∂Q, ‖E ω‖ ≤ F * ‖S ω‖ := by
    filter_upwards [hsol] with ω hω
    have h := parabolicSolution_cutoff_energy_le_scalar hK hI hU hω hζ hζc hζsupp hB
    have hv := mul_nonneg hB0 (measureReal_nonneg (μ := volume) (s := D))
    have hs := Real.sqrt_le_sqrt h
    rw [← heq ω, ← mul_assoc, Real.sqrt_mul hv] at hs
    simpa only [E, S, F, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hs
  refine ⟨hm.1.of_le_mul hEm.aestronglyMeasurable hdom, ?_⟩
  calc
    eLpNorm E (ENNReal.ofReal p) Q ≤ ENNReal.ofReal F * eLpNorm S (ENNReal.ofReal p) Q :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
    _ ≤ ENNReal.ofReal F * ENNReal.ofReal C := mul_le_mul_right hm.2 _
    _ = ENNReal.ofReal (F * C) := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm

end EinsteinRelation.Correctors
