import EinsteinRelation.External.AKMHeatKernel
import EinsteinRelation.Correctors.PairedPDEKernelBound
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Direct consequences of the AKM kernel contract

Source: `paper/main.tex:787–792,850`; AKM Proposition E.1, (E.3)–(E.4),
(E.10)–(E.11), printed pp. 499–501. These are implications from the
candidate contract, not proofs or approvals of that external proposition.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Positivity and unit mass in the orientation used for scalar evolution.
Source: AKM (E.4), p. 499; `paper/main.tex:850`. -/
theorem akm_heatKernel_mass {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C) (t : ℝ) (ht : 0 < t) (x : Vec d) :
    Integrable (P t x) volume ∧ (∀ᵐ y ∂volume, 0 ≤ P t x y) ∧
      (∫ y, P t x y ∂volume) = 1 := by
  exact ⟨(h.2.2.2.2.2.1 t ht x).1,
    Filter.Eventually.of_forall (h.2.1 t ht x),
    (h.2.2.2.2.2.1 t ht x).2.1⟩

/-- The scalar initial limit at a specified Lebesgue point, with the
orientation changed by symmetry. Source: AKM (E.3), (E.10)–(E.11),
pp. 499, 501; `paper/main.tex:850`. -/
theorem akm_heatKernel_initial_at_lebesgue_point {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C)
    {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) {x : Vec d}
    (hfG : ∃ k : ℝ, 0 ≤ k ∧
      Integrable (fun y => |f y| * Real.exp (-k * euclideanSq (y-x))) volume)
    (hx : IsHeatKernelLebesguePoint f x) :
    Tendsto (fun t => ∫ y, P t x y * f y ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (f x)) := by
  have hi := h.2.2.2.2.2.2.2.2 f hf x hfG hx
  apply hi.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change P t y x * f y = P t x y * f y
    rw [h.2.2.2.2.1 t ht y x]

/-- Equality of continuous scalar evolutions extends from almost every time
to every positive time. Source: `paper/main.tex:787–792,850`. -/
theorem akm_kernel_representation_of_ae_time
    {u v : ℝ → ℝ} (hu : ContinuousOn u (Set.Ioi 0))
    (hv : ContinuousOn v (Set.Ioi 0))
    (h : u =ᵐ[volume.restrict (Set.Ioi 0)] v) :
    ∀ t : ℝ, 0 < t → u t = v t := by
  exact Measure.eqOn_open_of_ae_eq h isOpen_Ioi hu hv

end EinsteinRelation.Correctors
