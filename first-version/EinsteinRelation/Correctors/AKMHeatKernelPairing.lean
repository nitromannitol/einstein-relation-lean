import EinsteinRelation.Correctors.AKMHeatKernelBounds
import EinsteinRelation.Correctors.AKMHeatKernelTimeContinuity

/-! # The forward/backward pairing of two AKM kernels

Source: `paper/main.tex:787–792,850`; the duality argument in the proof of
AKM Proposition E.1. All pairings use the actual continuous scalar kernels.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Every positive-time spatial slice is continuous on the whole space.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1. -/
theorem akm_heatKernel_space_continuous {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C) {t : ℝ} (ht : 0 < t) (y : Vec d) :
    Continuous (fun x => P t x y) := by
  apply continuousOn_univ.mp
  exact h.1.comp
    ((continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn)
    (fun _ _ => ⟨ht, Set.mem_univ _⟩)

/-- Every fixed spatial pair gives a continuous positive-time kernel slice.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1. -/
theorem akm_heatKernel_time_continuousOn {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C) (x y : Vec d) :
    ContinuousOn (fun t => P t x y) (Set.Ioi 0) := by
  exact h.1.comp ((continuous_id.prodMk (continuous_const :
    Continuous (fun _ : ℝ => (x,y)))).continuousOn)
    (fun t ht => ⟨ht, Set.mem_univ _⟩)

/-- A bounded measurable datum evolves continuously at positive times.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1, (E.3)–(E.4). -/
theorem akm_heatKernel_bounded_average_continuousOn {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C) (y : Vec d)
    {f : Vec d → ℝ} (hf : AEStronglyMeasurable f volume)
    {B : ℝ} (hB : ∀ᵐ z ∂volume, |f z| ≤ B) :
    ContinuousOn (fun t => ∫ z, P t z y * f z ∂volume) (Set.Ioi 0) := by
  exact akm_mass_one_kernel_average_continuousOn
    (fun z => akm_heatKernel_time_continuousOn h z y)
    (fun t ht => (h.2.2.2.2.2.1 t ht y).2.2.1)
    (fun t ht z => h.2.1 t ht z y)
    (fun t ht => (h.2.2.2.2.2.1 t ht y).2.2.2) hf hB

/-- The forward/backward pairing is absolutely integrable at each interior
time. Source: `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_pairing_integrable {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties A Q X₂ Y₂ H₂ C₂)
    {T s : ℝ} (hs : 0 < s) (hsT : s < T) (x y : Vec d) :
    Integrable (fun z => P s z y * Q (T-s) z x) volume := by
  exact (akm_heatKernel_slice_memLp hK hP hs y).integrable_mul
    (akm_heatKernel_slice_memLp hK hQ (sub_pos.mpr hsT) x)

end EinsteinRelation.Correctors
