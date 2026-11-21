import EinsteinFull.Regeneration.SlabShellRecurrence
import EinsteinFull.Regeneration.SlabProfileEnergyTransfer

/-!
# One step of the slab energy iteration

The comparison profile bound removes the remaining profile-energy term from
the nested-box recurrence.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The inner slab energy has an explicit boundary-layer plus shell-energy bound. -/
theorem slab_inset_energy_le_boundary_layer_add_shell
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ)
    (a b : PDE.Vec (n + 1)) (ha : a i = -L) (hb : b i = L)
    (w : ℝ) (hw : 0 < w)
    (hQ : PDE.IsOpenBoundedConvexDomain (PDE.axisBox a b))
    (hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U)
    (hQsource : PDE.axisBox a b ⊆ coordinateSlabBox n i s L)
    (hsource : coordinateSlabBox n i s L ⊆ U)
    (hKcube : slabShellSection i a b w ⊆
      Icc (fun _ => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k)
    (hthin : ∀ k, a i + δ k < b i - δ k)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hzero : ∀ x, 0 ≤ u x) (hone : ∀ x, u x ≤ 1)
    (hleft : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (a i, z)) = 0)
    (hright : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (b i, z)) = 1)
    (A : PDE.CoeffField (n + 1)) (lam' Λ' : ℝ)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x) U u 0 0)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x))
    (hsym : ∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) :
    let Q := PDE.axisBox a b
    let I := PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)
    let K : ℝ := (32 * (n + 1 : ℝ)) / w
    let α : ℝ := Λ * (K ^ 2 + K)
    let β : ℝ := 2 * Λ * K
    let A₀ : ℝ := Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))
    IntegrableOn (slabWeightedEnergy A s i u.grad) I ∧
    IntegrableOn (slabWeightedEnergy A s i u.grad) (Q \ I) ∧
    (∫ x in I, slabWeightedEnergy A s i u.grad x) ≤
      (Λ + α + β) * A₀ + ((α * (2 * L) ^ 2 + β) / lam) *
        ∫ x in Q \ I, slabWeightedEnergy A s i u.grad x := by
  dsimp only
  have hstep := slab_inset_energy_le_profile_add_shell hU u i L s lam Λ hL hs hlam hΛ
    a b ha hb w hw hQ hclosed hKcube δ hδ hδpos hthin hr hball hcont hzero hone
    hleft hright A lam' Λ' hsol hEll hA hsym
  have hprofile := slab_profile_energy_on_subbox_le hU i L s lam Λ lam' Λ' hL hs hΛ
    a b hQsource hsource A hEll hA
  dsimp only at hstep
  refine ⟨hstep.1, hstep.2.2.1, ?_⟩
  nlinarith [hstep.2.2.2, hprofile.2]

end EinsteinFull.Regeneration
