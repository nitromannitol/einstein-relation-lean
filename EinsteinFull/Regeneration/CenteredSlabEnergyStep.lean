import EinsteinFull.Regeneration.SlabEnergyStep
import EinsteinFull.Regeneration.SlabNestedGeometry

/-!
# Energy step for centered slabs

A transverse cutoff on a centered slab relates its energy to the energy of
the concentric slab with half the transverse side.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The open slab with a fixed force interval and centered transverse box. -/
def centeredSlabBox {d : ℕ} (i : Fin d) (L R : ℝ) : Set (PDE.Vec d) :=
  PDE.axisBox (centeredSlabLower i L R) (centeredSlabUpper i L R)

/-- A centered slab energy step with explicit cutoff constants. -/
theorem centered_slab_energy_step
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ R : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s)
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
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x) U u 0 0)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x))
    (hsym : ∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) :
    let K : ℝ := (32 * (n + 1 : ℝ)) / (R / 2)
    let α : ℝ := Λ * (K ^ 2 + K)
    let β : ℝ := 2 * Λ * K
    let A₀ : ℝ := Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))
    IntegrableOn (slabWeightedEnergy A s i u.grad) (centeredSlabBox i L R) ∧
    IntegrableOn (slabWeightedEnergy A s i u.grad) (centeredSlabBox i L (R / 2)) ∧
    (∫ x in centeredSlabBox i L (R / 2), slabWeightedEnergy A s i u.grad x) ≤
      (Λ + α + β) * A₀ + ((α * (2 * L) ^ 2 + β) / lam) *
        ∫ x in centeredSlabBox i L R, slabWeightedEnergy A s i u.grad x := by
  dsimp only
  let a := centeredSlabLower i L R
  let b := centeredSlabUpper i L R
  let Q := PDE.axisBox a b
  let I := PDE.axisBox (slabInsetLower i a (R / 2)) (slabInsetUpper i b (R / 2))
  have ha : a i = -L := by simp [a, centeredSlabLower]
  have hb : b i = L := by simp [b, centeredSlabUpper]
  have hclosedSource : closedCoordinateBox i a b (a i) (b i) ⊆ coordinateSlabBox n i s L := by
    simpa only [a, b, centeredSlabLower, centeredSlabUpper, ite_true] using
      centeredSlab_closed_subset_source i s L R hRmax
  have hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U := hclosedSource.trans hsource
  have hQsource : Q ⊆ coordinateSlabBox n i s L :=
    (axisBox_subset_closedCoordinateBox i a b).trans hclosedSource
  have hKcube := centeredSlab_shell_subset_source_cube i s L R (R / 2) hRmax
  have hthin' : ∀ k, a i + δ k < b i - δ k := by simpa only [ha, hb] using hthin
  have hleft' : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (a i, z)) = 0 := by simpa only [ha] using hleft
  have hright' : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (b i, z)) = 1 := by simpa only [hb] using hright
  have hstep := slab_inset_energy_le_boundary_layer_add_shell hU u i L s lam Λ hL hs hlam hΛ
    a b ha hb (R / 2) (by positivity) (PDE.isOpenBoundedConvexDomain_axisBox a b) hclosed
    hQsource hsource hKcube δ hδ hδpos hthin' hr hball hcont hzero hone hleft' hright'
    A lam' Λ' hsol hEll hA hsym
  dsimp only at hstep
  have hQsub : Q ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  have hEU : IntegrableOn (slabWeightedEnergy A s i u.grad) U := by
    have h := PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll u.gradMemL2
    have heq : slabWeightedEnergy A s i u.grad = fun x =>
        PDE.vecDot (u.grad x) (PDE.matVecMul (Real.exp (s * x i) • A x) (u.grad x)) := by
      funext x
      dsimp [slabWeightedEnergy, matrixEnergy]
      rw [PDE.vecDot_comm]
    rw [heq]
    exact h
  have hnonneg : ∀ᵐ x ∂(volume.restrict Q), 0 ≤ slabWeightedEnergy A s i u.grad x := by
    filter_upwards [ae_restrict_mem (PDE.isOpen_axisBox a b).measurableSet] with x hx
    have hell := hEll.elliptic (hQsub hx)
    have h := hell.coercive (u.grad x)
    have h0 := mul_nonneg hell.lam_pos.le (PDE.vecNormSq_nonneg (u.grad x))
    exact h0.trans (by simpa only [slabWeightedEnergy, matrixEnergy, PDE.vecDot_comm] using h)
  have houter := hEU.mono_set hQsub
  have hshell : (∫ x in Q \ I, slabWeightedEnergy A s i u.grad x) ≤
      ∫ x in Q, slabWeightedEnergy A s i u.grad x :=
    setIntegral_mono_set houter hnonneg (Filter.Eventually.of_forall fun _ hx => hx.1)
  have hcoeff : 0 ≤ (Λ * (((32 * (n + 1 : ℝ)) / (R / 2)) ^ 2 +
      ((32 * (n + 1 : ℝ)) / (R / 2))) * (2 * L) ^ 2 +
      2 * Λ * ((32 * (n + 1 : ℝ)) / (R / 2))) / lam := by positivity
  have heqI : I = centeredSlabBox i L (R / 2) := slabInset_centeredSlab i L R
  refine ⟨houter, ?_, ?_⟩
  · rw [← heqI]
    exact hstep.1
  · rw [← heqI]
    have hmul := mul_le_mul_of_nonneg_left hshell hcoeff
    dsimp only [Q, I, a, b, centeredSlabBox] at hstep hmul ⊢
    nlinarith [hstep.2.2, hmul]

end EinsteinFull.Regeneration
