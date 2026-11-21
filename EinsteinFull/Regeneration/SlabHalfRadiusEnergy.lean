import EinsteinFull.Regeneration.SlabInitialScale
import EinsteinFull.Regeneration.SlabGeometricScale

/-!
# Initial energy at half the source radius

The full source box provides the transverse collar for the first energy
estimate; the resulting initial box has half the source radius.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The first inset energy has a uniform exponential envelope. -/
theorem slab_half_radius_energy_le
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ : ℝ) (hL : 1 ≤ L) (hs : 0 < s)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hsource : coordinateSlabBox n i s L ⊆ U)
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
    (hsol : ∃ hQU : centeredSlabBox i L (slabGeometricRadius n s L 0) ⊆ U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
        (centeredSlabBox i L (slabGeometricRadius n s L 0))
        (u.restrict (PDE.isOpen_axisBox _ _) hQU) 0 0)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x))
    (hsym : ∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) :
    let D := 3 * Λ * Real.exp s * 2 ^ n +
      2 * ((Λ + 4 * Λ ^ 2 / lam) * (4 * (64 * (n + 1 : ℝ)) ^ 2)) * (2 ^ n / s)
    IntegrableOn (slabWeightedEnergy A s i u.grad)
      (centeredSlabBox i L (slabGeometricRadius n s L 1)) ∧
    (∫ x in centeredSlabBox i L (slabGeometricRadius n s L 1),
      slabWeightedEnergy A s i u.grad x) ≤
      D * Real.exp ((s * (2 * (n + 1 : ℝ) - 1) / (n + 1)) * L) := by
  dsimp only
  let R := slabGeometricRadius n s L 0
  have hR : 0 < R := slabGeometricRadius_pos n s L 0
  have hRmax : R ≤ Real.exp (s * L / (n + 1)) := slabGeometricRadius_le_source n s L 0
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
  have hleftR := ae_restrict_of_ae_restrict_of_subset hRcube hleft
  have hrightR := ae_restrict_of_ae_restrict_of_subset hRcube hright
  have hδ := slab_force_collar_widths L (by linarith)
  have h := centered_slab_initial_energy_le hU u i L s lam Λ R hL hs hlam hΛ hR hRmax hsource
    (fun k => L / ((k : ℝ) + 2)) hδ.1 hδ.2.1 hδ.2.2 hr hball hcont hzero hone
    hleftR hrightR A lam' Λ' hsol hEll hA hsym
  have hscale := slab_initial_source_terms_le n s lam Λ L hs hlam hΛ hL
  dsimp only at h hscale
  have hRvalue : R = Real.exp (s * L / (n + 1)) := by simp [R, slabGeometricRadius]
  rw [hRvalue] at h
  have hRhalf : slabGeometricRadius n s L 1 = Real.exp (s * L / (n + 1)) / 2 := by
    simp [slabGeometricRadius]
  rw [hRhalf]
  exact ⟨h.1, h.2.trans hscale⟩

end EinsteinFull.Regeneration
