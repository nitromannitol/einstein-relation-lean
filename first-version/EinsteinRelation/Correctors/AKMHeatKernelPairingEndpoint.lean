import EinsteinRelation.Correctors.AKMHeatKernelPairing
import EinsteinRelation.Correctors.AKMHeatKernelUniformTime
import EinsteinRelation.Correctors.AKMHeatKernelContinuousData
import EinsteinRelation.Correctors.ProbabilityKernelUniformError
import EinsteinRelation.Correctors.AKMHeatKernelGaussianData

/-! # Initial endpoint of the AKM forward/backward pairing

Source: `paper/main.tex:787–792,850`; the duality proof of AKM
Proposition E.1. The estimates use only the actual kernel properties.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The pairing converges to the other kernel at its initial endpoint.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof, p. 510. -/
theorem akm_heatKernel_pairing_initial {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    {T : ℝ} (hT : 0 < T) (x y : Vec d) :
    Tendsto (fun s => ∫ z, P s z y * Q (T-s) z x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (Q T y x)) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hlt : ∀ᶠ s in l, s < T :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)
  have hsub : Tendsto (fun s : ℝ => T-s) l (𝓝 T) := by
    have hid : Tendsto (fun s : ℝ => s) l (𝓝 0) := continuousWithinAt_id.tendsto
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => T) l (𝓝 T)).sub hid
  have hqc := akm_heatKernel_space_continuous hQ hT x
  obtain ⟨B, _, hB⟩ := akm_heatKernel_uniform_bound hK hQ hT
  have hqb : ∀ᵐ z ∂volume, |Q T z x| ≤ B :=
    Filter.Eventually.of_forall fun z => hB T le_rfl z x
  have hini := hP.2.2.2.2.2.2.2.2 (fun z => Q T z x) hqc.locallyIntegrable y
    ⟨1, zero_le_one, by
      simpa only [neg_mul, one_mul] using
        akm_bounded_gaussian_integrable hqc.aestronglyMeasurable hqb y⟩
    (akm_continuous_isHeatKernelLebesguePoint hqc.continuousAt)
  have hp : ∀ᶠ s in l, Integrable (fun z => P s z y) volume ∧
      (∀ᵐ z ∂volume, 0 ≤ P s z y) ∧ (∫ z, P s z y ∂volume) = 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨(hP.2.2.2.2.2.1 s hs y).2.2.1,
      Filter.Eventually.of_forall (fun z => hP.2.1 s hs z y),
      (hP.2.2.2.2.2.1 s hs y).2.2.2⟩
  have he : ∀ᶠ s in l,
      AEStronglyMeasurable (fun z => Q (T-s) z x - Q T z x) volume := by
    filter_upwards [hlt] with s hs
    exact (akm_heatKernel_space_continuous hQ (sub_pos.mpr hs) x).aestronglyMeasurable.sub
      hqc.aestronglyMeasurable
  have herr := akm_probability_kernel_uniform_error hp he (by
    intro ε hε
    exact hsub.eventually (akm_heatKernel_uniform_time_continuity hK hQ T hT x ε hε))
  have hlim := herr.add hini
  simpa only [zero_add] using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin, hlt] with s hs hsT
    have hi := akm_heatKernel_pairing_integrable hK hP hQ hs hsT x y
    have hi₀ : Integrable (fun z => P s z y * Q T z x) volume :=
      (akm_heatKernel_slice_memLp hK hP hs y).integrable_mul
        (akm_heatKernel_slice_memLp hK hQ hT x)
    have heq : (∫ z, P s z y * (Q (T-s) z x-Q T z x) ∂volume) =
        (∫ z, P s z y * Q (T-s) z x ∂volume) -
          ∫ z, P s z y * Q T z x ∂volume := by
      rw [← integral_sub hi hi₀]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => mul_sub _ _ _
    rw [heq]
    ring)

end EinsteinRelation.Correctors
