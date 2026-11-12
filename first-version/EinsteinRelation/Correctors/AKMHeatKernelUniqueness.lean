import EinsteinRelation.Correctors.AKMHeatKernelPairingContinuity
import EinsteinRelation.Correctors.AKMHeatKernelPairingEndpoint
import EinsteinRelation.Correctors.AKMHeatKernelPairingWeak
import EinsteinRelation.Correctors.WeakTimeConstant
import EinsteinRelation.Correctors.AKMKernelGradientIdentification

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Forward/backward kernel duality preserves the spatial pairing.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1, proof on p. 510. -/
theorem akm_heatKernel_pairing_constant {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    {T : ℝ} (hT : 0 < T) (x y : Vec d) {s : ℝ} (hs : 0 < s) (hsT : s < T) :
    (∫ z, P s z y * Q (T-s) z x ∂volume) =
      ∫ z, P (T/2) z y * Q (T-T/2) z x ∂volume := by
  let F : ℝ → ℝ := fun t => ∫ z, P t z y * Q (T-t) z x ∂volume
  have hcont := akm_heatKernel_pairing_continuousOn hK hP hQ T x y
  have heq {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbT : b < T) : F b = F a := by
    apply endpoints_eq_of_integral_mul_deriv_eq_zero hab F
      (hcont.mono fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hbT⟩)
    intro η hη hηc hηs
    exact akm_heatKernel_pairing_weak hK hP hQ ha hab hbT x y hη hηc hηs
  rcases lt_trichotomy s (T/2) with h | h | h
  · exact (heq hs h (half_lt_self hT)).symm
  · rw [h]
  · exact heq (half_pos hT) h hsT

/-- The point-mass initial trace evaluates the constant pairing.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1, proof on p. 510. -/
theorem akm_heatKernel_pairing_midpoint_eq {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    {T : ℝ} (hT : 0 < T) (x y : Vec d) :
    (∫ z, P (T/2) z y * Q (T-T/2) z x ∂volume) = Q T y x := by
  have hlim := akm_heatKernel_pairing_initial hK hP hQ hT x y
  have hconst : Tendsto (fun s => ∫ z, P s z y * Q (T-s) z x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (∫ z, P (T/2) z y * Q (T-T/2) z x ∂volume)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with s hs hsT
    exact (akm_heatKernel_pairing_constant hK hP hQ hT x y hs hsT).symm
  exact tendsto_nhds_unique hconst hlim

/-- AKM E.1 properties determine the scalar heat kernel at every positive time.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1, proof on p. 510. -/
theorem akm_heatKernel_unique {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂) :
    ∀ t : ℝ, 0 < t → ∀ x y : Vec d, P t x y = Q t x y := by
  intro t ht x y
  have hPQ := akm_heatKernel_pairing_midpoint_eq hK hP hQ ht x y
  have hQP := akm_heatKernel_pairing_midpoint_eq hK hQ hP ht y x
  have hm : t-t/2 = t/2 := by ring
  rw [hm] at hPQ hQP
  have heq : (∫ z, P (t/2) z y * Q (t/2) z x ∂volume) =
      ∫ z, Q (t/2) z x * P (t/2) z y ∂volume := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => mul_comm _ _
  exact hQP.symm.trans (heq.symm.trans (hPQ.trans (hQ.2.2.2.2.1 t ht y x)))

/-- Heat-kernel uniqueness identifies every continuous flow represented
using their actual weak gradients. Source: `paper/main.tex:787–792,850`;
AKM (9.2). -/
theorem akm_kernel_represented_flows_eq {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K}
    {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    {g : Vec d → Vec d} {u v : ℝ × Vec d → ℝ}
    (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    (hv : ContinuousOn v (Set.Ioi 0 ×ˢ Set.univ))
    (hurep : ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      u (t,x) = -(∫ y, dot (g y) (Y₁ t x y) ∂volume))
    (hvrep : ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      v (t,x) = -(∫ y, dot (g y) (Y₂ t x y) ∂volume)) :
    ∀ t : ℝ, 0 < t → ∀ x : Vec d, u (t,x) = v (t,x) := by
  exact akm_kernel_represented_flows_eq_of_kernels_eq hP hQ
    (akm_heatKernel_unique hK hP hQ) hu hv hurep hvrep

end EinsteinRelation.Correctors
