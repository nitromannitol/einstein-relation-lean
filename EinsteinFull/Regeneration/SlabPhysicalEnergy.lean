import EinsteinFull.Regeneration.SlabHarnackEnergy
import EinsteinRelation.External.GantertSection7Support

/-!
# Physical-force slab energy

The unit-force reversible density is the exponential weight used in the
central-box energy estimate.
-/

open MeasureTheory Set PDE EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The unit-force equation has the large-slab energy lower bound. -/
theorem exists_physical_slab_box_energy_lower_of_harnack
    (n : ℕ) (hd : 2 ≤ n + 1) (lam Λ : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ) :
    let i := firstCoordinateIndex hd
    ∃ c L₀ : ℝ, 0 < c ∧ 0 < L₀ ∧ ∀ (L : ℝ), L₀ ≤ L →
      ∀ {U : Set (PDE.Vec (n + 1))} (a : PDE.CoeffField (n + 1)) (u : PDE.H1Function U),
      IsOpen U → coordinateSlabBox n i 2 L ⊆ U →
      (∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
        (fun x => physicalForceWeight hd 1 x • a x)) →
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => physicalForceWeight hd 1 x • a x)
        U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → u 0 < 2 / 3 →
      (∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
        PDE.HasWeakDerivOnIoo 0 L (fun t => u (centralSlabPoint n i (t, z)))
          (fun t => u.grad (centralSlabPoint n i (t, z)) i) ∧
        u (centralSlabPoint n i (L, z)) = 1) →
      lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ x in coordinateSlabBox n i 2 L,
        PDE.vecDot (PDE.matVecMul (physicalForceWeight hd 1 x • a x) (u.grad x)) (u.grad x) := by
  obtain ⟨c, L₀, hc, hL₀, hbound⟩ :=
    exists_slab_box_energy_lower_of_harnack n lam Λ 2 hlam hΛ (by norm_num)
  refine ⟨c, L₀, hc, hL₀, ?_⟩
  intro L hL U a u hU hbox hEll hmeas hA hsol hcont hupper hsmall hslice
  have h := hbound (firstCoordinateIndex hd) L hL a u hU hbox
  simp only [physicalForceWeight, mul_one] at hEll hsol ⊢
  exact h hEll hmeas hA hsol hcont hupper hsmall hslice

end EinsteinFull.Regeneration
