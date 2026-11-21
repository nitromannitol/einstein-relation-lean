import EinsteinFull.Regeneration.SlabIncrementEnergy

/-!
# Harnack energy for continuous Sobolev solutions

The Sobolev increment theorem removes separate weak-slice assumptions from
the central slab energy estimate.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Harnack and the Sobolev increment theorem give the central energy lower bound. -/
theorem exists_central_slab_energy_lower_of_harnack_of_h1
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
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • a x) U u 0 0 →
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
  have hlocal := weak_divergence_form_l2_solution_restrict hsol hU.isOpen hBopen hBU
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


/-- Harnack gives the full-box energy bound for a continuous Sobolev solution. -/
theorem exists_slab_box_energy_lower_of_harnack_of_h1
    (n : ℕ) (lam Λ s : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ) (hs : 0 < s) :
    ∃ c L₀ : ℝ, 0 < c ∧ 0 < L₀ ∧ ∀ (i : Fin (n + 1)) (L : ℝ), L₀ ≤ L →
      ∀ {U : Set (PDE.Vec (n + 1))} (a : PDE.CoeffField (n + 1)) (u : PDE.H1Function U),
      PDE.IsOpenBoundedConvexDomain U → coordinateSlabBox n i s L ⊆ U →
      (∃ x₀ : PDE.Vec (n + 1), ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ U) →
      (∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
        (fun x => Real.exp (s * x i) • a x)) →
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → u 0 < 2 / 3 →
      (∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
        u (centralSlabPoint n i (L, z)) = 1) →
      lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ x in coordinateSlabBox n i s L,
        PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x) (u.grad x)) (u.grad x) := by
  obtain ⟨c, hc, henergy⟩ :=
    exists_central_slab_energy_lower_of_harnack_of_h1 n lam Λ s hlam hΛ hs
  obtain ⟨L₀, hL₀, hsides⟩ := exists_large_slab_sides n s hs
  refine ⟨c, L₀, hc, hL₀, ?_⟩
  intro i L hL U a u hU hbox hball hEll hmeas hA hsol hcont hupper hsmall hslice
  have hLpos : 0 < L := hL₀.trans_le hL
  obtain ⟨hside, htrans⟩ := hsides L hL
  have htrans' : 1 ≤ Real.exp (s * L / (n + 1)) := by
    have hR : 0 ≤ Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)) := Real.sqrt_nonneg _
    linarith
  have hcentral : coordinateCentralSlab n i L ⊆ coordinateSlabBox n i s L :=
    coordinateCentralSlab_subset_slabBox n i s L hLpos.le htrans'
  have hballs : ∀ z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1),
      PDE.euclideanBall
        ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
        (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ U := by
    intro z hz
    exact (central_comparison_ball_subset_slab_box n i s L z hz hside htrans).trans hbox
  have hlow := henergy i L hLpos a u hU (hcentral.trans hbox) hball hballs hEll
    hmeas hA hsol hcont hupper hsmall hslice
  let f : PDE.Vec (n + 1) → ℝ := fun x =>
    PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x) (u.grad x)) (u.grad x)
  obtain ⟨lam', Λ', hEll'⟩ := hEll
  have hf : IntegrableOn f (coordinateSlabBox n i s L) := by
    have h := PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll' u.gradMemL2
    simpa only [f, PDE.vecDot_comm] using h.mono_set hbox
  have hboxmeas : MeasurableSet (coordinateSlabBox n i s L) := by
    exact (measurableSet_Icc.prod measurableSet_Icc).preimage
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable
  have hfnonneg : ∀ᵐ x ∂(volume.restrict (coordinateSlabBox n i s L)), 0 ≤ f x := by
    filter_upwards [ae_restrict_mem hboxmeas] with x hx
    have h := (hEll'.elliptic (hbox hx)).coercive (u.grad x)
    have hp := (hEll'.elliptic (hbox hx)).lam_pos
    have hq := PDE.vecNormSq_nonneg (u.grad x)
    dsimp only [f]
    rw [PDE.vecDot_comm]
    nlinarith
  have hmono : (∫ x in coordinateCentralSlab n i L, f x) ≤
      ∫ x in coordinateSlabBox n i s L, f x :=
    setIntegral_mono_set hf hfnonneg (Filter.Eventually.of_forall fun _ hx => hcentral hx)
  exact hlow.trans (mul_le_mul_of_nonneg_left hmono hLpos.le)

end EinsteinFull.Regeneration
