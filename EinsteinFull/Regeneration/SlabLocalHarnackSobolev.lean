import EinsteinFull.Regeneration.SlabIncrementEnergy

/-!
# Harnack energy from local comparison-ball equations

The Sobolev increment theorem removes separate weak-slice assumptions from
the central slab energy estimate.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Harnack and the Sobolev increment theorem give the central energy lower bound. -/
theorem exists_central_slab_energy_lower_of_local_harnack
    (n : ℕ) (lam Λ s : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ) (hs : 0 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin (n + 1)) (L : ℝ), 0 < L →
      ∀ {U : Set (PDE.Vec (n + 1))} (a : PDE.CoeffField (n + 1)) (u : PDE.H1Function U),
      PDE.IsOpenBoundedConvexDomain U → coordinateCentralSlab n i L ⊆ U →
      (∃ x₀ : PDE.Vec (n + 1), ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ U) →
      (∀ z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1),
        PDE.euclideanBall
          ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
          (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ U) →
      (∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
        (fun x => Real.exp (s * x i) • a x)) →
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      (∀ z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1),
        ∀ hBU : PDE.euclideanBall
          ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
          (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ U,
        PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • a x)
          (PDE.euclideanBall
            ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
            (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))))
          (u.restrict (PDE.isOpen_euclideanBall _ _) hBU) 0 0) →
      Continuous u.toFun → (∀ x, u x ≤ 1) → u 0 < 2 / 3 →
      (∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
        u (centralSlabPoint n i (L, z)) = 1) →
      lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ x in coordinateCentralSlab n i L,
        PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x) (u.grad x)) (u.grad x) := by
  obtain ⟨c, hc, hcompare⟩ :=
    gmp_central_cube_complement_lower_of_force (n + 1) (by omega) lam Λ s hlam hΛ hs
  refine ⟨c, hc, ?_⟩
  intro i L hL U a u hU hsub ⟨x₀, r, hr, hclosed⟩ hball hEll hmeas hA hsol hcont hupper hsmall hslice
  apply coordinate_central_slab_energy_lower_of_h1 n i L c lam Λ s
    hL hc.le hlam hs.le hU a u hsub hr hclosed hEll hA hcont
  filter_upwards [ae_restrict_mem measurableSet_Icc, hslice] with z hz hface
  let x := centralSlabPoint n i (0, z)
  let B := PDE.euclideanBall ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + x))
    (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)))
  have hBopen : IsOpen B := PDE.isOpen_euclideanBall _ _
  have hBU : B ⊆ U := hball z hz
  have hlocal := hsol z hz hBU
  have hA' : ∀ᵐ y ∂(volume.restrict B), PDE.IsEllipticMatrix lam Λ (a y) :=
    ae_restrict_of_ae_restrict_of_subset hBU hA
  have hm' (j k : Fin (n + 1)) : AEMeasurable (fun y => a y j k) (volume.restrict B) :=
    (hmeas j k).mono_measure (Measure.restrict_mono hBU le_rfl)
  have hcub : ∀ j, |x j| ≤ 1 := centralSlabPoint_abs_le_one n i z hz
  have hx : x i = 0 := (centralSlabPoint_coord n i 0 z).1
  have hcmp := hcompare i x hx hcub
  dsimp only at hcmp
  have hgap := hcmp a hm' hA' (u.restrict hBopen hBU) hlocal hcont hupper hsmall
  exact ⟨hgap, hface⟩



end EinsteinFull.Regeneration
