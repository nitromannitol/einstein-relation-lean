import EinsteinFull.Regeneration.SlabGeometricLocalRecurrence
import EinsteinFull.Regeneration.SlabEnergyIteration

/-!
# Iteration of the actual slab energies

The source-scale recurrence for weighted energies yields a small terminal
energy once the initial energy has the standard exponential bound.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The actual geometric slab energies become smaller than any prescribed
reciprocal-width threshold under the initial energy estimate. -/
theorem exists_slab_width_of_local_energy_recurrence
    (n : ℕ) (s lam Λ D c : ℝ) (hs : 0 < s) (hlam : 0 < lam)
    (hΛ : 0 ≤ Λ) (hc : 0 < c) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ (U : Set (PDE.Vec (n + 1)))
      (_hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U) (i : Fin (n + 1)),
      coordinateSlabBox n i s L ⊆ U →
      ∀ {x₀ : PDE.Vec (n + 1)} {r : ℝ}, 0 < r → Metric.closedBall x₀ r ⊆ U →
      Continuous u.toFun → (∀ x, 0 ≤ u x) → (∀ x, u x ≤ 1) →
      (∀ᵐ z ∂(volume.restrict
        (Icc (fun _ : Fin n => -Real.exp (s * L / (n + 1)))
          (fun _ => Real.exp (s * L / (n + 1))))),
        u (centralSlabPoint n i (-L, z)) = 0) →
      (∀ᵐ z ∂(volume.restrict
        (Icc (fun _ : Fin n => -Real.exp (s * L / (n + 1)))
          (fun _ => Real.exp (s * L / (n + 1))))),
        u (centralSlabPoint n i (L, z)) = 1) →
      ∀ (A : PDE.CoeffField (n + 1)) (lam' Λ' : ℝ),
      (∀ j < 2 * (n + 1), ∃ hQU :
        centeredSlabBox i L (slabGeometricRadius n s L j) ⊆ U,
        PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
          (centeredSlabBox i L (slabGeometricRadius n s L j))
          (u.restrict (PDE.isOpen_axisBox _ _) hQU) 0 0) →
      PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x) →
      (∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x)) →
      (∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) →
      (∫ x in centeredSlabBox i L (slabGeometricRadius n s L 0),
        slabWeightedEnergy A s i u.grad x) ≤
        D * Real.exp ((s * (2 * ((n + 1 : ℕ) : ℝ) - 1) / (n + 1)) * L) →
      L * (∫ x in centeredSlabBox i L (slabGeometricRadius n s L (2 * (n + 1))),
        slabWeightedEnergy A s i u.grad x) < c := by
  let C : ℝ := 32 * (n + 1 : ℝ) * (2 : ℝ) ^ (2 * (n + 1))
  let A₀ : ℝ := (Real.exp s * 2 ^ n) * Λ * (1 + C ^ 2 + 3 * C)
  let B₀ : ℝ := Λ * (4 * C ^ 2 + 6 * C) / lam
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀, C]; positivity
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀, C]; positivity
  obtain ⟨L₀, hL₀⟩ := exists_slab_width_of_force_energy_recurrence (n + 1) (by omega)
    s A₀ B₀ D c hs hA₀ hB₀ hc
  refine ⟨max L₀ 1, ?_⟩
  intro L hL U hU u i hsource x₀ r hr hball hcont hzero hone hleft hright A lam' Λ'
    hsol hEll hA hsym hinit
  have hLlarge : L₀ ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  let E : ℕ → ℝ := fun j => ∫ x in centeredSlabBox i L (slabGeometricRadius n s L j),
    slabWeightedEnergy A s i u.grad x
  have hsteps := slab_geometric_energy_recurrence_of_local_solutions hU u i L s lam Λ hL1 hs.le hlam hΛ
    hsource hr hball hcont hzero hone hleft hright A lam' Λ' hsol hEll hA hsym
  dsimp only at hsteps
  apply hL₀ L hLlarge E
  · intro j hj
    simpa only [E, A₀, B₀, C, Nat.cast_add, Nat.cast_one] using (hsteps.2.2 j hj).2.2
  · simpa only [E, Nat.cast_add, Nat.cast_one] using hinit

end EinsteinFull.Regeneration
