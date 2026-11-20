import EinsteinFull.Regeneration.SlabCutoffLocalMinimality
import EinsteinFull.Regeneration.SlabTransverseCutoff

/-!
# Local energy minimality for the transverse cutoff

The explicit transverse cutoff supplies the admissibility needed for the
slab energy comparison.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The symmetric solution's energy is bounded by the energy of the explicit
transverse cutoff competitor. -/
theorem slab_energy_le_transverse_competitor_of_local_solution
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L : ℝ) (hL : 1 ≤ L)
    (a b : PDE.Vec (n + 1)) (ha : a i = -L) (hb : b i = L)
    (w : ℝ) (hw : 0 < w)
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
    (A : PDE.CoeffField (n + 1)) (lam Λ : ℝ)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn A (PDE.axisBox a b)
      (u.restrict hQ.isOpen ((axisBox_subset_closedCoordinateBox i a b).trans hclosed)) 0 0)
    (hEll : PDE.IsEllipticFieldOn lam Λ (PDE.axisBox a b) A)
    (hsym : ∀ᵐ x ∂(PDE.volumeOn (PDE.axisBox a b)), (A x).IsSymm) :
    IntegrableOn (fun x => PDE.vecDot
      (PDE.matVecMul (A x) (u.grad x +
        (slabCutoffPerturbation hU u i L (slabTransverseCutoff i a b w hw)).grad x))
      (u.grad x + (slabCutoffPerturbation hU u i L (slabTransverseCutoff i a b w hw)).grad x))
      (PDE.axisBox a b) ∧
    (∫ x in PDE.axisBox a b, PDE.vecDot (PDE.matVecMul (A x) (u.grad x)) (u.grad x)) ≤
      ∫ x in PDE.axisBox a b, PDE.vecDot
        (PDE.matVecMul (A x) (u.grad x +
          (slabCutoffPerturbation hU u i L (slabTransverseCutoff i a b w hw)).grad x))
        (u.grad x + (slabCutoffPerturbation hU u i L (slabTransverseCutoff i a b w hw)).grad x) := by
  apply slab_energy_le_cutoff_competitor_of_local_solution hU u i L hL (slabTransverseCutoff i a b w hw)
    a b ha hb hQ hclosed δ hδ hδpos hthin hr hball hcont hleft hright ?_ A lam Λ hsol hEll hsym
  intro j hji
  refine ⟨w / 2, by positivity, ?_⟩
  intro x _ hx
  exact slabTransverseCutoff_lateral_zero i a b w hw j hji x hx

end EinsteinFull.Regeneration
