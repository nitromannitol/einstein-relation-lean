import EinsteinFull.Regeneration.SlabCutoffPerturbation
import EinsteinFull.Regeneration.SlabEnergyMinimality

/-!
# Local energy minimality for a slab cutoff

The solution need only satisfy the weak equation on the comparison box; its
Sobolev representative may extend to a larger ambient domain.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A locally elliptic solution has no larger box energy than the admissible
slab cutoff competitor. -/
theorem slab_energy_le_cutoff_competitor_of_local_solution
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
      ∀ x ∈ PDE.axisBox a b, x ∈ boxFaceCollars a b j ρ → η x = 0)
    (A : PDE.CoeffField (n + 1)) (lam Λ : ℝ)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn A (PDE.axisBox a b)
      (u.restrict hQ.isOpen ((axisBox_subset_closedCoordinateBox i a b).trans hclosed)) 0 0)
    (hEll : PDE.IsEllipticFieldOn lam Λ (PDE.axisBox a b) A)
    (hsym : ∀ᵐ x ∂(PDE.volumeOn (PDE.axisBox a b)), (A x).IsSymm) :
    IntegrableOn (fun x => PDE.vecDot
      (PDE.matVecMul (A x) (u.grad x + (slabCutoffPerturbation hU u i L η).grad x))
      (u.grad x + (slabCutoffPerturbation hU u i L η).grad x)) (PDE.axisBox a b) ∧
    (∫ x in PDE.axisBox a b, PDE.vecDot (PDE.matVecMul (A x) (u.grad x)) (u.grad x)) ≤
      ∫ x in PDE.axisBox a b, PDE.vecDot
        (PDE.matVecMul (A x) (u.grad x + (slabCutoffPerturbation hU u i L η).grad x))
        (u.grad x + (slabCutoffPerturbation hU u i L η).grad x) := by
  have hQsub : PDE.axisBox a b ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  let uQ := u.restrict hQ.isOpen hQsub
  obtain ⟨v, _, hvgrad⟩ := exists_h10_slabCutoffPerturbation hU u i L hL η a b ha hb
    hQ hclosed δ hδ hδpos hthin hr hball hcont hleft hright hlateral
  obtain ⟨hint, hbound⟩ := elliptic_energy_le_of_symmetric_ellipticity A uQ hsol v hEll hsym
  have heq : ∀ᵐ x ∂(PDE.volumeOn (PDE.axisBox a b)),
      PDE.vecDot (PDE.matVecMul (A x) (uQ.grad x + v.toH1Function.grad x))
        (uQ.grad x + v.toH1Function.grad x) =
      PDE.vecDot (PDE.matVecMul (A x) (u.grad x + (slabCutoffPerturbation hU u i L η).grad x))
        (u.grad x + (slabCutoffPerturbation hU u i L η).grad x) := by
    filter_upwards [hvgrad] with x hx
    rw [hx]
    rfl
  refine ⟨hint.congr heq, ?_⟩
  rw [← integral_congr_ae heq]
  exact hbound

end EinsteinFull.Regeneration
