import EinsteinFull.Regeneration.SlabCentralCubeTransfer
import EinsteinFull.Regeneration.GMPForceHarnack

/-!
# Harnack and central-slab energy

The local comparison estimate supplies the central gap needed for the
Gantert–Mathieu–Piatnitski energy argument.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- An `L²` weak solution restricts to an open subdomain. -/
theorem weak_divergence_form_l2_solution_restrict {d : ℕ}
    {a : PDE.CoeffField d} {U V : Set (PDE.Vec d)} {u : PDE.H1Function U}
    {f : PDE.Vec d → ℝ} {F : PDE.Vec d → PDE.Vec d}
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u f F)
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) :
    PDE.IsWeakDivergenceFormL2SolutionOn a V (u.restrict hV hVU) f F where
  flux_memL2 := fun j => (hsol.flux_memL2 j).mono_measure
    (Measure.restrict_mono hVU le_rfl)
  source_memL2 := hsol.source_memL2.mono_measure (Measure.restrict_mono hVU le_rfl)
  forcing_memL2 := fun j => (hsol.forcing_memL2 j).mono_measure
    (Measure.restrict_mono hVU le_rfl)
  identity := fun φ => (hsol.toIsWeakDivergenceFormSolutionOn.restrict hU hV hVU φ).2

/-- A central slice point has zero force coordinate and the transverse coordinates supplied. -/
theorem centralSlabPoint_coord (n : ℕ) (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) :
    centralSlabPoint n i (t, z) i = t ∧
      ∀ j, centralSlabPoint n i (t, z) (i.succAbove j) = z j := by
  constructor
  · simp [centralSlabPoint, MeasurableEquiv.piFinSuccAbove_symm_apply]
  · intro j
    simp [centralSlabPoint, MeasurableEquiv.piFinSuccAbove_symm_apply]

/-- A transverse unit-cube point gives a central vector in the unit cube. -/
theorem centralSlabPoint_abs_le_one (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℝ)
    (hz : z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)) :
    ∀ j, |centralSlabPoint n i (0, z) j| ≤ 1 := by
  intro j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simp [centralSlabPoint_coord]
  · rw [(centralSlabPoint_coord n i 0 z).2 k]
    exact abs_le.mpr ⟨hz.1 k, hz.2 k⟩

/-- Harnack supplies a uniform central gap for the physical central-slab energy bound. -/
theorem exists_central_slab_energy_lower_of_harnack
    (n : ℕ) (lam Λ s : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ) (hs : 0 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin (n + 1)) (L : ℝ), 0 < L →
      ∀ {U : Set (PDE.Vec (n + 1))} (a : PDE.CoeffField (n + 1)) (u : PDE.H1Function U),
      IsOpen U → coordinateCentralSlab n i L ⊆ U →
      (∀ z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1),
        PDE.euclideanBall
          ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
          (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ U) →
      (∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
        (fun x => Real.exp (s * x i) • a x)) →
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → u 0 < 2 / 3 →
      (∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
        ContinuousOn (fun t => u (centralSlabPoint n i (t, z))) (Icc 0 L) ∧
        PDE.HasWeakDerivOnIoo 0 L (fun t => u (centralSlabPoint n i (t, z)))
          (fun t => u.grad (centralSlabPoint n i (t, z)) i) ∧
        u (centralSlabPoint n i (L, z)) = 1) →
      lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ x in coordinateCentralSlab n i L,
        PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x) (u.grad x)) (u.grad x) := by
  obtain ⟨c, hc, hcompare⟩ :=
    gmp_central_cube_complement_lower_of_force (n + 1) (by omega) lam Λ s hlam hΛ hs
  refine ⟨c, hc, ?_⟩
  intro i L hL U a u hU hsub hball hEll hmeas hA hsol hcont hupper hsmall hslice
  apply coordinate_central_slab_energy_lower_of_weak_slices n i L c lam Λ s
    hL hc.le hlam hs.le a u hsub hEll hA
  filter_upwards [ae_restrict_mem measurableSet_Icc, hslice] with z hz ⟨hline, hweak, hface⟩
  let x := centralSlabPoint n i (0, z)
  let B := PDE.euclideanBall ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + x))
    (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)))
  have hBopen : IsOpen B := PDE.isOpen_euclideanBall _ _
  have hBU : B ⊆ U := hball z hz
  have hlocal := weak_divergence_form_l2_solution_restrict hsol hU hBopen hBU
  have hA' : ∀ᵐ y ∂(volume.restrict B), PDE.IsEllipticMatrix lam Λ (a y) :=
    ae_restrict_of_ae_restrict_of_subset hBU hA
  have hm' (j k : Fin (n + 1)) : AEMeasurable (fun y => a y j k) (volume.restrict B) :=
    (hmeas j k).mono_measure (Measure.restrict_mono hBU le_rfl)
  have hcub : ∀ j, |x j| ≤ 1 := centralSlabPoint_abs_le_one n i z hz
  have hx : x i = 0 := (centralSlabPoint_coord n i 0 z).1
  have hcmp := hcompare i x hx hcub
  dsimp only at hcmp
  have hgap := hcmp a hm' hA' (u.restrict hBopen hBU) hlocal hcont hupper hsmall
  exact ⟨hline, hweak, hgap, hface⟩

end EinsteinFull.Regeneration
