import EinsteinRelation.Correctors.AKMHeatKernelConsequences
import EinsteinRelation.Correctors.AKMHeatKernelEnergySlices
import EinsteinRelation.Calculus.WeakGradientUniqueness

/-! # Identification of represented flows from their scalar kernels

Source: `paper/main.tex:787–792,850`; AKM (9.2) and Proposition E.1.
Spatial weak-gradient uniqueness first identifies kernel derivatives at
almost every time. Continuity then identifies the represented scalar
flows at every positive time.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Equal scalar kernels have equal second spatial gradients at almost
every positive time and almost every spatial point.
Source: `paper/main.tex:787–792,850`; AKM (9.2). -/
theorem akm_heatKernel_second_gradients_eq_ae_time {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    (heq : ∀ t : ℝ, 0 < t → ∀ x y : Vec d, P t x y = Q t x y)
    (x : Vec d) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
      (fun y => Y₁ t x y) =ᵐ[volume] (fun y => Y₂ t x y) := by
  have hp := akm_fundamental_energy_slices (hP.2.2.2.1 x).1
  have hq := akm_fundamental_energy_slices (hQ.2.2.2.1 x).1
  filter_upwards [hp, hq, ae_restrict_mem measurableSet_Ioi] with t hpt hqt ht
  have hscalar : (fun y => P t x y) = (fun y => Q t x y) := funext (heq t ht x)
  apply hpt.1.ae_eq_of_same_potential
  rw [hscalar]
  exact hqt.1

/-- Equality of scalar kernels identifies every continuous flow represented
using their actual weak gradients. Source: `paper/main.tex:787–792,850`;
AKM (9.2). -/
theorem akm_kernel_represented_flows_eq_of_kernels_eq {d : ℕ} {K : ℝ}
    {A : Coefficient d K}
    {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    (heq : ∀ t : ℝ, 0 < t → ∀ x y : Vec d, P t x y = Q t x y)
    {g : Vec d → Vec d} {u v : ℝ × Vec d → ℝ}
    (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    (hv : ContinuousOn v (Set.Ioi 0 ×ˢ Set.univ))
    (hurep : ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      u (t,x) = -(∫ y, dot (g y) (Y₁ t x y) ∂volume))
    (hvrep : ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      v (t,x) = -(∫ y, dot (g y) (Y₂ t x y) ∂volume)) :
    ∀ t : ℝ, 0 < t → ∀ x : Vec d, u (t,x) = v (t,x) := by
  intro t ht x
  have huc : ContinuousOn (fun s => u (s,x)) (Set.Ioi 0) :=
    hu.comp ((continuous_id.prodMk continuous_const).continuousOn)
      (fun s hs => ⟨hs, Set.mem_univ _⟩)
  have hvc : ContinuousOn (fun s => v (s,x)) (Set.Ioi 0) :=
    hv.comp ((continuous_id.prodMk continuous_const).continuousOn)
      (fun s hs => ⟨hs, Set.mem_univ _⟩)
  apply akm_kernel_representation_of_ae_time huc hvc ?_ t ht
  filter_upwards [akm_heatKernel_second_gradients_eq_ae_time hP hQ heq x,
    ae_restrict_mem measurableSet_Ioi] with s hs hspos
  rw [hurep s hspos x, hvrep s hspos x]
  congr 1
  apply integral_congr_ae
  filter_upwards [hs] with y hy
  rw [hy]

end EinsteinRelation.Correctors
