import EinsteinRelation.Correctors.AKMHeatKernelPairing
import EinsteinRelation.Correctors.AKMHeatKernelUniformTime
import EinsteinRelation.Correctors.ProbabilityKernelUniformError

/-! # Continuity of the AKM forward/backward pairing

Source: `paper/main.tex:787–792,850`; the duality proof of AKM
Proposition E.1. The estimates use only the actual kernel properties.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The forward/backward pairing is continuous between its endpoints.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof, p. 510. -/
theorem akm_heatKernel_pairing_continuousOn {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    (T : ℝ) (x y : Vec d) :
    ContinuousOn (fun s => ∫ z, P s z y * Q (T-s) z x ∂volume) (Set.Ioo 0 T) := by
  intro s hs
  let l := nhdsWithin s (Set.Ioo 0 T)
  have hsT : 0 < T-s := sub_pos.mpr hs.2
  obtain ⟨B, _, hB⟩ := akm_heatKernel_uniform_bound hK hQ hsT
  have hqc := akm_heatKernel_space_continuous hQ hsT x
  have hfixed := akm_mass_one_kernel_average_continuousOn
    (fun z => akm_heatKernel_time_continuousOn hP z y)
    (fun t ht => (hP.2.2.2.2.2.1 t ht y).2.2.1)
    (fun t ht z => hP.2.1 t ht z y)
    (fun t ht => (hP.2.2.2.2.2.1 t ht y).2.2.2)
    hqc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => hB (T-s) le_rfl z x))
  have hfixedlim : Tendsto (fun r => ∫ z, P r z y * Q (T-s) z x ∂volume) l
      (𝓝 (∫ z, P s z y * Q (T-s) z x ∂volume)) :=
    ((hfixed s hs.1).mono (fun _ hr => hr.1)).tendsto
  have hsub : Tendsto (fun r : ℝ => T-r) l (𝓝 (T-s)) :=
    tendsto_const_nhds.sub continuousWithinAt_id.tendsto
  have hp : ∀ᶠ r in l, Integrable (fun z => P r z y) volume ∧
      (∀ᵐ z ∂volume, 0 ≤ P r z y) ∧ (∫ z, P r z y ∂volume) = 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ⟨(hP.2.2.2.2.2.1 r hr.1 y).2.2.1,
      Filter.Eventually.of_forall (fun z => hP.2.1 r hr.1 z y),
      (hP.2.2.2.2.2.1 r hr.1 y).2.2.2⟩
  have he : ∀ᶠ r in l,
      AEStronglyMeasurable (fun z => Q (T-r) z x - Q (T-s) z x) volume := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (akm_heatKernel_space_continuous hQ (sub_pos.mpr hr.2) x).aestronglyMeasurable.sub
      hqc.aestronglyMeasurable
  have herr := akm_probability_kernel_uniform_error hp he (by
    intro ε hε
    exact hsub.eventually
      (akm_heatKernel_uniform_time_continuity hK hQ (T-s) hsT x ε hε))
  have hlim := herr.add hfixedlim
  apply (show Tendsto _ l _ from ?_)
  simpa only [zero_add] using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hi := akm_heatKernel_pairing_integrable hK hP hQ hr.1 hr.2 x y
    have hi₀ : Integrable (fun z => P r z y * Q (T-s) z x) volume :=
      (akm_heatKernel_slice_memLp hK hP hr.1 y).integrable_mul
        (akm_heatKernel_slice_memLp hK hQ hsT x)
    have heq : (∫ z, P r z y * (Q (T-r) z x-Q (T-s) z x) ∂volume) =
        (∫ z, P r z y * Q (T-r) z x ∂volume) -
          ∫ z, P r z y * Q (T-s) z x ∂volume := by
      rw [← integral_sub hi hi₀]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => mul_sub _ _ _
    rw [heq]
    ring)

end EinsteinRelation.Correctors
