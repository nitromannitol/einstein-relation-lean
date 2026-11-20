import EinsteinFull.Regeneration.SlabZeroBoundary
import EinsteinFull.Regeneration.ZeroBoundaryGradient
import EinsteinFull.Regeneration.SlabBoundaryProfile
import PDEFoundation.Sobolev.H1.Algebra
import PDEFoundation.Sobolev.H1.Cutoff

/-!
# The slab cutoff perturbation

A transverse cutoff times the difference between the comparison profile and
the solution has zero boundary values on the comparison box.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The Sobolev perturbation used in the slab energy comparison. -/
noncomputable def slabCutoffPerturbation {n : ℕ} {U inner outer : Set (PDE.Vec (n + 1))}
    {C : ℝ} (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L : ℝ) (η : PDE.QuantitativeSmoothCutoff inner outer C) :
    PDE.H1Function U := ((slabBoundaryProfile hU i L) - u).mulCutoff η

/-- The comparison perturbation has an admissible zero-boundary representative
with the same weak gradient on the comparison box. -/
theorem exists_h10_slabCutoffPerturbation
    {n : ℕ} {U inner outer : Set (PDE.Vec (n + 1))} {C : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L : ℝ) (hL : 1 ≤ L)
    (η : PDE.QuantitativeSmoothCutoff inner outer C)
    (a b : PDE.Vec (n + 1)) (ha : a i = -L) (hb : b i = L)
    (hQ : PDE.IsOpenBoundedConvexDomain (PDE.axisBox a b))
    (hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k)
    (hthin : ∀ k, a i + δ k < b i - δ k)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hleft : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (a i, z)) = 0)
    (hright : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (b i, z)) = 1)
    (hlateral : ∀ j : Fin (n + 1), j ≠ i → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ PDE.axisBox a b, x ∈ boxFaceCollars a b j ρ → η x = 0) :
    ∃ v : PDE.H10Function (PDE.axisBox a b),
      v.toH1Function.toFun = (slabCutoffPerturbation hU u i L η).toFun ∧
      ∀ᵐ x ∂(PDE.volumeOn (PDE.axisBox a b)),
        v.toH1Function.grad x = (slabCutoffPerturbation hU u i L η).grad x := by
  let w := slabCutoffPerturbation hU u i L η
  have hw_apply (x : PDE.Vec (n + 1)) : w x = η x * (slabBoundaryProfile hU i L x - u x) := by
    simp [w, slabCutoffPerturbation]
  have hprofilecont : Continuous (slabBoundaryProfile hU i L).toFun := by
    have heq : (slabBoundaryProfile hU i L).toFun =
        fun x => min (max (x i + L) 0) 1 := by
      funext x
      exact slabBoundaryProfile_apply hU i L x
    rw [heq]
    exact (((continuous_apply i).add continuous_const).max continuous_const).min continuous_const
  have hwcont : Continuous w.toFun := by
    have heq : w.toFun = fun x => η x * (slabBoundaryProfile hU i L x - u x) := by
      funext x
      exact hw_apply x
    rw [heq]
    exact η.smooth.continuous.mul (hprofilecont.sub hcont)
  have hwleft : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      w (centralSlabPoint n i (a i, z)) = 0 := by
    filter_upwards [hleft] with z hz
    have hc := (centralSlabPoint_coord n i (a i) z).1
    have hp : slabBoundaryProfile hU i L (centralSlabPoint n i (a i, z)) = 0 :=
      slabBoundaryProfile_eq_zero hU i L _ (by rw [hc, ha])
    rw [hw_apply, hp, hz]
    ring
  have hwright : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      w (centralSlabPoint n i (b i, z)) = 0 := by
    filter_upwards [hright] with z hz
    have hc := (centralSlabPoint_coord n i (b i) z).1
    have hp : slabBoundaryProfile hU i L (centralSlabPoint n i (b i, z)) = 1 :=
      slabBoundaryProfile_eq_one hU i L _ (by rw [hc, hb]; linarith)
    rw [hw_apply, hp, hz]
    ring
  have hwlateral : ∀ j : Fin (n + 1), j ≠ i → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ PDE.axisBox a b, x ∈ boxFaceCollars a b j ρ → w x = 0 := by
    intro j hji
    obtain ⟨ρ, hρ, hzero⟩ := hlateral j hji
    refine ⟨ρ, hρ, ?_⟩
    intro x hx hc
    rw [hw_apply, hzero x hx hc, zero_mul]
  have hw : PDE.MemH10 (PDE.axisBox a b) w.toFun :=
    memH10_box_of_force_faces_and_lateral_support hU w i a b hQ hclosed δ hδ hδpos hthin
      hr hball hwcont hwleft hwright hwlateral
  have hQsub : PDE.axisBox a b ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  let wQ := w.restrict hQ.isOpen hQsub
  exact exists_h10_with_ae_gradient hQ.isOpen wQ hw

end EinsteinFull.Regeneration
