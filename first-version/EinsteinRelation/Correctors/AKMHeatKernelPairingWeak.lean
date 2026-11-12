import EinsteinRelation.Correctors.AKMHeatKernelBounds
import EinsteinRelation.Correctors.AKMHeatKernelCutoffLocalization
import EinsteinRelation.Correctors.AKMHeatKernelGlobalGradient
import EinsteinRelation.Correctors.ParabolicTimeReflection
import EinsteinRelation.Correctors.ParabolicDualityFlux
import EinsteinRelation.Correctors.ParabolicDualityCutoffRemoval
import EinsteinRelation.Correctors.ParabolicDualityTesting
import EinsteinRelation.Correctors.PairedPDETimeSlope

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The mixed kernel pairing has zero weak derivative on every interior time interval.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1, proof on p. 510. -/
theorem akm_heatKernel_pairing_weak {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    {a b T : ℝ} (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (x y : Vec d) {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Set.Ioo a b) :
    (∫ t in a..b, (∫ z, P t z y * Q (T-t) z x ∂volume) * deriv η t) = 0 := by
  let u : ℝ × Vec d → ℝ := fun z => P z.1 z.2 y
  let v : ℝ × Vec d → ℝ := fun z => Q (T-z.1) z.2 x
  let G : ℝ × Vec d → Vec d := fun z => X₁ z.1 z.2 y
  let H : ℝ × Vec d → Vec d := fun z => X₂ (T-z.1) z.2 x
  let μ := volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))
  have htr := akm_time_reflection_strip_measurePreserving d T a b
  have hu : MemLp u 2 μ := akm_heatKernel_strip_memLp hK hP ha y
  have hv : MemLp v 2 μ := by
    simpa only [v, Function.comp_def] using
      (akm_heatKernel_strip_memLp hK hQ (sub_pos.mpr hbT) x).comp_measurePreserving htr
  obtain ⟨hGm, hG⟩ := akm_heatKernel_global_gradient_memLp hK hP ha hab y
  obtain ⟨hHm₀, hH₀⟩ := akm_heatKernel_global_gradient_memLp hK hQ
    (sub_pos.mpr hbT) (by linarith : T-b < T-a) x
  have hHm : AEStronglyMeasurable H μ := by
    simpa only [H, Function.comp_def] using hHm₀.comp_measurePreserving htr
  have hH : MemLp (fun z => euclideanNorm (H z)) 2 μ := by
    simpa only [H, Function.comp_def] using hH₀.comp_measurePreserving htr
  let F : ℝ × Vec d → Vec d := fun z j =>
    v z * ((A z.2).mulVec (G z)) j - u z * ((A z.2).mulVec (H z)) j
  have hF (j : Fin d) : Integrable (fun z => F z j) μ :=
    akm_global_duality_flux_integrable hK A hu hv hGm hHm hG hH j
  obtain ⟨B, _, hB, _⟩ := paired_compact_time_slope_bound hη hηc
  have hηd : AEStronglyMeasurable (fun z : ℝ × Vec d => deriv η z.1) μ :=
    ((hη.continuous_deriv (by simp)).comp continuous_fst).aestronglyMeasurable
  have hf : Integrable (fun z => u z * v z * deriv η z.1) μ :=
    (hu.integrable_mul hv).mul_bdd hηd (Filter.Eventually.of_forall (fun z => hB z.1))
  have hz : (∫ z in Set.Ioo a b ×ˢ Set.univ, u z * v z * deriv η z.1) = 0 := by
    apply akm_global_duality_cutoff_removal hf hF hη.continuous hηc
    intro χ hχ hχc
    obtain ⟨n, hn⟩ := akm_compact_subset_originBall hχc
    have hR : 0 < (n+1 : ℝ) := by positivity
    have hid := parabolicSolutions_forward_backward_cutoff_pairing hK hab hR
      ((hP.2.2.1 y).1 a b (n+1) ha hab hR)
      ((hQ.2.2.1 x).1 (T-b) (T-a) (n+1) (sub_pos.mpr hbT) (by linarith) hR)
      hη hηc hηs ⟨hχ, hχc, hn⟩
    rw [akm_spatially_supported_strip_integral measurableSet_Ioo hn
      (f := fun z => u z * v z * deriv η z.1 * χ z.2 ^ 2)
      (fun z hz => by simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero]),
      akm_spatially_supported_strip_integral measurableSet_Ioo hn
        (f := fun z => η z.1 * χ z.2 * dot (F z) (gradient χ z.2))
        (fun z hz => by simp only [hz, mul_zero, zero_mul])]
    exact hid.2.2
  have hprod : μ = (volume.restrict (Set.Ioo a b)).prod (volume : Measure (Vec d)) := by
    dsimp only [μ]
    change ((volume : Measure ℝ).prod volume).restrict (Set.Ioo a b ×ˢ Set.univ) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  change (∫ t in Set.Ioo a b, (∫ z, u (t,z) * v (t,z)) * deriv η t) = 0
  have hfprod := hf
  rw [hprod] at hfprod
  have heq := integral_prod (fun z => u z * v z * deriv η z.1) hfprod
  simp only [integral_mul_const] at heq
  apply heq.symm.trans
  rw [← hprod]
  exact hz

end EinsteinRelation.Correctors
