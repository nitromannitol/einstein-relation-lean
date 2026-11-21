import EinsteinFull.Regeneration.SlabShellErrors
import EinsteinFull.Regeneration.SlabShellArithmetic

/-!
# Energy recurrence on nested slab boxes

The actual cutoff comparison and shell-error bounds combine into an explicit
recurrence involving the profile energy and the solution's shell energy.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The weighted energy on a transverse inset is controlled by the profile
energy, boundary-layer mass and solution energy on the shell. -/
theorem slab_inset_energy_le_profile_add_shell
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ)
    (a b : PDE.Vec (n + 1)) (ha : a i = -L) (hb : b i = L)
    (w : ℝ) (hw : 0 < w)
    (hQ : PDE.IsOpenBoundedConvexDomain (PDE.axisBox a b))
    (hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U)
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
    let p := slabBoundaryProfile hU i L
    let K : ℝ := (32 * (n + 1 : ℝ)) / w
    let α : ℝ := Λ * (K ^ 2 + K)
    let β : ℝ := 2 * Λ * K
    let A₀ : ℝ := Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))
    IntegrableOn (slabWeightedEnergy A s i u.grad) I ∧
    IntegrableOn (slabWeightedEnergy A s i p.grad) Q ∧
    IntegrableOn (slabWeightedEnergy A s i u.grad) (Q \ I) ∧
    (∫ x in I, slabWeightedEnergy A s i u.grad x) ≤
      (∫ x in Q, slabWeightedEnergy A s i p.grad x) + (α + β) * A₀ +
        ((α * (2 * L) ^ 2 + β) / lam) *
          ∫ x in Q \ I, slabWeightedEnergy A s i u.grad x := by
  dsimp only
  let Q := PDE.axisBox a b
  let I := PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)
  let p := slabBoundaryProfile hU i L
  let K : ℝ := (32 * (n + 1 : ℝ)) / w
  let α : ℝ := Λ * (K ^ 2 + K)
  let β : ℝ := 2 * Λ * K
  let A₀ : ℝ := Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))
  have hQsub : Q ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  have hEllQ := hEll.mono hQ.measurableSet hQsub
  have hAQ : ∀ᵐ x ∂(PDE.volumeOn Q), PDE.IsEllipticMatrix lam Λ (A x) :=
    ae_restrict_of_ae_restrict_of_subset hQsub hA
  have hsymQ : ∀ᵐ x ∂(PDE.volumeOn Q), (A x).IsSymm :=
    ae_restrict_of_ae_restrict_of_subset hQsub hsym
  have henergy := slab_inset_energy_le_shell_errors hU u i L s hL hs a b ha hb w hw hQ hclosed
    δ hδ hδpos hthin hr hball hcont hleft hright A lam Λ lam' Λ' hsol hEllQ hAQ hsymQ
  have hrightL : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (L, z)) = 1 := by simpa only [hb] using hright
  have herrors := slab_shell_errors_le_energy hU u i L s lam Λ hL hs hlam a b ha hb w hclosed
    hKcube hr hball hcont hzero hone hrightL A ⟨lam', Λ', hEll⟩ hA
  dsimp only at henergy herrors
  have hT : (∫ x in Q \ I, Real.exp (s * x i) * (p x - u x) ^ 2) =
      ∫ x in Q \ I, Real.exp (s * x i) * (u x - p x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    ring
  have hS : (∫ x in Q \ I, Real.exp (s * x i) *
      (PDE.vecNormSq (p.grad x) + PDE.vecNormSq (u.grad x))) =
      ∫ x in Q \ I, Real.exp (s * x i) *
        (PDE.vecNormSq (u.grad x) + PDE.vecNormSq (p.grad x)) := by
    simp only [add_comm]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hα : 0 ≤ α := mul_nonneg hΛ (add_nonneg (sq_nonneg K) hK)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hmain := slab_shell_substitution
    (∫ x in I, slabWeightedEnergy A s i u.grad x)
    (∫ x in Q, slabWeightedEnergy A s i p.grad x) α β
    (∫ x in Q \ I, Real.exp (s * x i) * (u x - p x) ^ 2)
    (∫ x in Q \ I, Real.exp (s * x i) *
      (PDE.vecNormSq (u.grad x) + PDE.vecNormSq (p.grad x)))
    lam A₀ ((2 * L) ^ 2) (∫ x in Q \ I, slabWeightedEnergy A s i u.grad x)
    hlam hα hβ herrors.2.2.2.1 herrors.2.2.2.2 (by
      rw [hT, hS] at henergy
      exact henergy.2.2.2.2)
  refine ⟨henergy.1.mono_set (slabInsetBox_subset i a b w hw.le), henergy.2.1,
    herrors.2.2.1, hmain⟩

end EinsteinFull.Regeneration
