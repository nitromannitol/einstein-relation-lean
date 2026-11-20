import EinsteinFull.Regeneration.BoxForceCollar

/-!
# Zero boundary values for slab perturbations

Zero force-face values and support away from the transverse faces make a
continuous Sobolev perturbation admissible for the box energy comparison.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A continuous Sobolev function vanishing on the force faces and near all
transverse faces has a zero-boundary restriction to the box. -/
theorem memH10_box_of_force_faces_and_lateral_support
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (a b : PDE.Vec (n + 1))
    (hQ : PDE.IsOpenBoundedConvexDomain (PDE.axisBox a b))
    (hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k)
    (hthin : ∀ k, a i + δ k < b i - δ k)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hleft : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (a i, z)) = 0)
    (hright : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (b i, z)) = 0)
    (hlateral : ∀ j : Fin (n + 1), j ≠ i → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ PDE.axisBox a b, x ∈ boxFaceCollars a b j ρ → u x = 0) :
    PDE.MemH10 (PDE.axisBox a b) u.toFun := by
  have hQsub : PDE.axisBox a b ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  let v : PDE.H1Function (PDE.axisBox a b) := u.restrict hQ.isOpen hQsub
  have hv : PDE.MemH10 (PDE.axisBox a b) v.toFun := by
    apply memH10_of_box_face_collars a b hQ v δ hδ hδpos
    intro j
    by_cases hji : j = i
    · subst j
      exact tendsto_box_force_collar_normalized hU u i a b hclosed δ hδ hδpos hthin
        hr hball hcont hleft hright
    · obtain ⟨ρ, hρ, hzero⟩ := hlateral j hji
      exact tendsto_box_face_collar_of_vanishes_near_faces a b j hQ.measurableSet
        u.toFun ρ hρ hzero δ hδ
  exact hv

end EinsteinFull.Regeneration
