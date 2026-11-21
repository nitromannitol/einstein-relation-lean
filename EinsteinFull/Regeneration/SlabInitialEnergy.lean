import EinsteinFull.Regeneration.SlabCaccioppoli
import EinsteinFull.Regeneration.SlabInitialValueError
import EinsteinFull.Regeneration.SlabProfileEnergyTransfer
import EinsteinFull.Regeneration.SlabNestedGeometry
import EinsteinFull.Regeneration.CenteredSlabEnergyStep

/-!
# Initial energy of a centered slab

The boundary Caccioppoli estimate, the profile energy, and the full-box
value error give an explicit bound on the half-radius slab.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The half-radius energy is controlled by explicit source-box terms. -/
theorem centered_slab_initial_energy_le
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ R : ℝ) (hL : 1 ≤ L) (hs : 0 < s)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hR : 0 < R)
    (hRmax : R ≤ Real.exp (s * L / (n + 1)))
    (hsource : coordinateSlabBox n i s L ⊆ U)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k)
    (hthin : ∀ k, -L + δ k < L - δ k)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hzero : ∀ x, 0 ≤ u x) (hone : ∀ x, u x ≤ 1)
    (hleft : ∀ᵐ z ∂(volume.restrict
      (transverseClosedBox i (centeredSlabLower i L R) (centeredSlabUpper i L R))),
      u (centralSlabPoint n i (-L, z)) = 0)
    (hright : ∀ᵐ z ∂(volume.restrict
      (transverseClosedBox i (centeredSlabLower i L R) (centeredSlabUpper i L R))),
      u (centralSlabPoint n i (L, z)) = 1)
    (A : PDE.CoeffField (n + 1)) (lam' Λ' : ℝ)
    (hsol : ∃ hQU : centeredSlabBox i L R ⊆ U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
        (centeredSlabBox i L R) (u.restrict (PDE.isOpen_axisBox _ _) hQU) 0 0)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x))
    (hsym : ∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) :
    let α := (Λ + 4 * Λ ^ 2 / lam) * (4 * ((32 * (n + 1 : ℝ)) / (R / 2)) ^ 2)
    IntegrableOn (slabWeightedEnergy A s i u.grad) (centeredSlabBox i L (R / 2)) ∧
    (∫ x in centeredSlabBox i L (R / 2), slabWeightedEnergy A s i u.grad x) ≤
      3 * (Λ * (Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1))))) +
      2 * α * (((2 : ℝ) ^ n / s) *
        Real.exp ((s * (2 * (n + 1 : ℝ) - 1) / (n + 1)) * L)) := by
  dsimp only
  let a := centeredSlabLower i L R
  let b := centeredSlabUpper i L R
  let Q := PDE.axisBox a b
  let α : ℝ := (Λ + 4 * Λ ^ 2 / lam) * (4 * ((32 * (n + 1 : ℝ)) / (R / 2)) ^ 2)
  have ha : a i = -L := by simp [a, centeredSlabLower]
  have hb : b i = L := by simp [b, centeredSlabUpper]
  have hclosedSource : closedCoordinateBox i a b (a i) (b i) ⊆ coordinateSlabBox n i s L := by
    simpa only [a, b, centeredSlabLower, centeredSlabUpper, ite_true] using
      centeredSlab_closed_subset_source i s L R hRmax
  have hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U := hclosedSource.trans hsource
  have hQsource : Q ⊆ coordinateSlabBox n i s L :=
    (axisBox_subset_closedCoordinateBox i a b).trans hclosedSource
  have hQU : Q ⊆ U := hQsource.trans hsource
  have hqopen := PDE.isOpenBoundedConvexDomain_axisBox a b
  have hthin' : ∀ k, a i + δ k < b i - δ k := by simpa only [ha, hb] using hthin
  have hleft' : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (a i, z)) = 0 := by simpa only [ha] using hleft
  have hright' : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (b i, z)) = 1 := by simpa only [hb] using hright
  obtain ⟨_, hsolQ⟩ := hsol
  have hA' := ae_restrict_of_ae_restrict_of_subset hQU hA
  have hsym' := ae_restrict_of_ae_restrict_of_subset hQU hsym
  have hEllQ := hEll.mono hqopen.measurableSet hQU
  have hcacc := slab_inset_energy_le_profile_and_value_error hU u i L s hL a b ha hb
    (R / 2) (by positivity) hqopen hclosed δ hδ hδpos hthin' hr hball hcont hleft' hright'
    A lam Λ lam' Λ' hsolQ hEllQ hA' hsym'
  have hprof := slab_profile_energy_on_subbox_le hU i L s lam Λ lam' Λ' hL hs.le hΛ
    a b hQsource hsource A hEll hA
  have herr := slab_profile_value_error_le_initial_rate hU u i L s hs a b hQsource hcont hzero hone
  have hα : 0 ≤ α := by
    dsimp [α]
    exact mul_nonneg (add_nonneg hΛ (div_nonneg (by positivity) hlam.le)) (by positivity)
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hprof.2 (by norm_num : (0 : ℝ) ≤ 3))
    (mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 2 * α))
  have hI : PDE.axisBox (slabInsetLower i a (R / 2)) (slabInsetUpper i b (R / 2)) =
      centeredSlabBox i L (R / 2) := slabInset_centeredSlab i L R
  dsimp only at hcacc
  rw [hI] at hcacc
  exact ⟨hcacc.1, hcacc.2.trans hsum⟩

end EinsteinFull.Regeneration
