import EinsteinFull.Regeneration.SlabGeometricGeneralScale
import EinsteinFull.Regeneration.CenteredSlabLocalNormalizedStep

/-!
# Finite geometric recurrence for actual slab energies

The centered one-step estimate holds uniformly for the finite sequence of
transverse radii in the slab energy argument.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The finite geometric family of centered slab energies satisfies the
source-scale recurrence with constants fixed before the box index. -/
theorem slab_geometric_energy_recurrence_of_local_solutions_up_to
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (N : ℕ) (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ)
    (hsource : coordinateSlabBox n i s L ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hzero : ∀ x, 0 ≤ u x) (hone : ∀ x, u x ≤ 1)
    (hleft : ∀ᵐ z ∂(volume.restrict
      (Icc (fun _ : Fin n => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))))),
      u (centralSlabPoint n i (-L, z)) = 0)
    (hright : ∀ᵐ z ∂(volume.restrict
      (Icc (fun _ : Fin n => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))))),
      u (centralSlabPoint n i (L, z)) = 1)
    (A : PDE.CoeffField (n + 1)) (lam' Λ' : ℝ)
    (hsol : ∀ j < N, ∃ hQU :
      centeredSlabBox i L (slabGeometricRadius n s L j) ⊆ U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
        (centeredSlabBox i L (slabGeometricRadius n s L j))
        (u.restrict (PDE.isOpen_axisBox _ _) hQU) 0 0)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x))
    (hsym : ∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) :
    let C : ℝ := 32 * (n + 1 : ℝ) * (2 : ℝ) ^ N
    let A₀ : ℝ := (Real.exp s * 2 ^ n) * Λ * (1 + C ^ 2 + 3 * C)
    let B₀ : ℝ := Λ * (4 * C ^ 2 + 6 * C) / lam
    0 ≤ A₀ ∧ 0 ≤ B₀ ∧ ∀ j < N,
      IntegrableOn (slabWeightedEnergy A s i u.grad)
        (centeredSlabBox i L (slabGeometricRadius n s L j)) ∧
      IntegrableOn (slabWeightedEnergy A s i u.grad)
        (centeredSlabBox i L (slabGeometricRadius n s L (j + 1))) ∧
      (∫ x in centeredSlabBox i L (slabGeometricRadius n s L (j + 1)),
        slabWeightedEnergy A s i u.grad x) ≤
        A₀ * Real.exp (-(s * L / (n + 1))) +
        B₀ * L ^ 2 * Real.exp (-(s * L / (n + 1))) *
          ∫ x in centeredSlabBox i L (slabGeometricRadius n s L j),
            slabWeightedEnergy A s i u.grad x := by
  dsimp only
  let C : ℝ := 32 * (n + 1 : ℝ) * (2 : ℝ) ^ N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA₀ : 0 ≤ (Real.exp s * 2 ^ n) * Λ * (1 + C ^ 2 + 3 * C) := by positivity
  have hB₀ : 0 ≤ Λ * (4 * C ^ 2 + 6 * C) / lam := by positivity
  refine ⟨hA₀, hB₀, ?_⟩
  intro j hj
  let R := slabGeometricRadius n s L j
  have hR : 0 < R := slabGeometricRadius_pos n s L j
  have hRmax : R ≤ Real.exp (s * L / (n + 1)) := slabGeometricRadius_le_source n s L j
  have hRcube : transverseClosedBox i (centeredSlabLower i L R) (centeredSlabUpper i L R) ⊆
      Icc (fun _ : Fin n => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))) := by
    intro z hz
    constructor <;> intro k
    · have h := hz.1 k
      simp only [centeredSlabLower, Fin.succAbove_ne, ite_false] at h
      linarith
    · have h := hz.2 k
      simp only [centeredSlabUpper, Fin.succAbove_ne, ite_false] at h
      linarith
  have hleftR : ∀ᵐ z ∂(volume.restrict
      (transverseClosedBox i (centeredSlabLower i L R) (centeredSlabUpper i L R))),
      u (centralSlabPoint n i (-L, z)) = 0 :=
    ae_restrict_of_ae_restrict_of_subset hRcube hleft
  have hrightR : ∀ᵐ z ∂(volume.restrict
      (transverseClosedBox i (centeredSlabLower i L R) (centeredSlabUpper i L R))),
      u (centralSlabPoint n i (L, z)) = 1 :=
    ae_restrict_of_ae_restrict_of_subset hRcube hright
  have hδ := slab_force_collar_widths L (by linarith)
  have hstep := centered_slab_energy_normalized_step_of_local_solution hU u i L s lam Λ R C hL hs hlam hΛ hR hC
    hRmax (slabGeometricRadius_gradient_le_of_lt n N s L j hj) hsource
    (fun k => L / ((k : ℝ) + 2)) hδ.1 hδ.2.1 hδ.2.2 hr hball hcont hzero hone
    hleftR hrightR A lam' Λ' (hsol j hj) hEll hA hsym
  rw [← slabGeometricRadius_succ n s L j] at hstep
  exact hstep

end EinsteinFull.Regeneration
