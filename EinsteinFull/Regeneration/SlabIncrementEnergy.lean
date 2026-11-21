import EinsteinFull.Regeneration.SlabSobolevIncrement

/-!
# Slab energy from Sobolev line increments

Endpoint increments give the central-box coercive energy estimate in the
Gantert–Mathieu–Piatnitski argument.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Central endpoint increments, a central gap and the right-face value bound the energy. -/
theorem central_slab_energy_lower_of_increments
    (n : ℕ) (L c lam : ℝ) (hL : 0 < L) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (u g ρ : ℝ × (Fin n → ℝ) → ℝ)
    (hg : MemLp g 2 (centralSlabMeasure n L))
    (hρ : Integrable ρ (centralSlabMeasure n L))
    (hslice : ∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
      u (L, z) - u (0, z) = ∫ t in (0 : ℝ)..L, g (t, z) ∧
      c ≤ 1 - u (0, z) ∧ u (L, z) = 1)
    (hcoercive : ∀ᵐ p ∂(centralSlabMeasure n L), lam * g p ^ 2 ≤ ρ p) :
    lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ p, ρ p ∂(centralSlabMeasure n L) := by
  let V : Set (Fin n → ℝ) := Icc (fun _ => -1) (fun _ => 1)
  let ν : Measure (Fin n → ℝ) := volume.restrict V
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hmeasure : ν.real univ = (2 : ℝ) ^ n := by
    have h := volume_transverse_cube n 1 (by norm_num)
    simpa [ν, V, measureReal_def] using h
  have hinc : ∀ᵐ z ∂ν, u (L, z) - u (0, z) = ∫ t in (0 : ℝ)..L, g (t, z) := by
    filter_upwards [hslice] with z hz
    exact hz.1
  have hgap : ∀ᵐ z ∂ν, c ≤ |u (L, z) - u (0, z)| := by
    filter_upwards [hslice] with z ⟨_, hcenter, hface⟩
    rw [hface]
    exact hcenter.trans (le_abs_self _)
  have h := slab_coercive_energy_lower_of_increments ν L c lam
    hL.le hc hlam u g ρ hg hρ hinc hgap hcoercive
  simpa only [hmeasure, centralSlabMeasure, ν, V] using h

/-- The central-slab bound transfers through physical coordinates. -/
theorem coordinate_central_slab_energy_lower_of_increments
    (n : ℕ) (i : Fin (n + 1)) (L c lam Λ s : ℝ)
    (hL : 0 < L) (hc : 0 ≤ c) (hlam : 0 < lam) (hs : 0 ≤ s)
    {U : Set (PDE.Vec (n + 1))} (a : PDE.CoeffField (n + 1)) (u : PDE.H1Function U)
    (hsub : coordinateCentralSlab n i L ⊆ U)
    (hEll : ∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
      (fun x => Real.exp (s * x i) • a x))
    (hA : ∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x))
    (hslice : ∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
      u (centralSlabPoint n i (L, z)) - u (centralSlabPoint n i (0, z)) =
        ∫ t in (0 : ℝ)..L, u.grad (centralSlabPoint n i (t, z)) i ∧
      c ≤ 1 - u (centralSlabPoint n i (0, z)) ∧
      u (centralSlabPoint n i (L, z)) = 1) :
    lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ x in coordinateCentralSlab n i L,
      PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x) (u.grad x)) (u.grad x) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let V : Set (ℝ × (Fin n → ℝ)) := Ioc 0 L ×ˢ Icc (fun _ => -1) (fun _ => 1)
  let W := coordinateCentralSlab n i L
  let f : PDE.Vec (n + 1) → ℝ := fun x =>
    PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x) (u.grad x)) (u.grad x)
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' W = V := by
    ext p
    simp [W, coordinateCentralSlab, e, V]
  have hWmeas : MeasurableSet W :=
    (measurableSet_Ioc.prod measurableSet_Icc).preimage
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable
  have hm : (volume : Measure (ℝ × (Fin n → ℝ))).restrict V = centralSlabMeasure n L := by
    dsimp only [V, centralSlabMeasure]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, hm] at hpresW
  have hg : MemLp (fun p => u.grad (e p) i) 2 (centralSlabMeasure n L) := by
    have h := (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
    exact h.comp_measurePreserving hpresW
  obtain ⟨lam', Λ', hEll'⟩ := hEll
  have hρU : IntegrableOn f U := by
    simpa only [f, PDE.vecDot_comm] using
      PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll' u.gradMemL2
  have hρ : Integrable (fun p => f (e p)) (centralSlabMeasure n L) := by
    rw [← hm, ← hpre]
    exact (hpres.integrableOn_comp_preimage e.measurableEmbedding).2 (hρU.mono_set hsub)
  have hAe : ∀ᵐ p ∂(centralSlabMeasure n L), PDE.IsEllipticMatrix lam Λ (a (e p)) :=
    hpresW.quasiMeasurePreserving.ae (ae_restrict_of_ae_restrict_of_subset hsub hA)
  have ht : ∀ᵐ p ∂(centralSlabMeasure n L), 0 ≤ p.1 := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc 0 L))
      (ν := volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)))).ae
        (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [h] with p hp
    exact hp.1.le
  have hcoercive : ∀ᵐ p ∂(centralSlabMeasure n L),
      lam * (u.grad (e p) i) ^ 2 ≤ f (e p) := by
    filter_upwards [hAe, ht] with p hp hpt
    have he : (e p) i = p.1 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    simpa only [f, he] using weighted_energy_coercive_coordinate i s p.1 lam Λ hs hpt
      (a (e p)) hp (u.grad (e p))
  have hslices : ∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
      u (e (L, z)) - u (e (0, z)) = ∫ t in (0 : ℝ)..L, u.grad (e (t, z)) i ∧
      c ≤ 1 - u (e (0, z)) ∧ u (e (L, z)) = 1 := by
    simpa only [e, centralSlabPoint] using hslice
  have h := central_slab_energy_lower_of_increments n L c lam hL hc hlam.le
    (fun p => u (e p)) (fun p => u.grad (e p) i) (fun p => f (e p))
    hg hρ hslices hcoercive
  have heq : (∫ x in W, f x) = ∫ p, f (e p) ∂centralSlabMeasure n L := by
    rw [← hpresW.map_eq]
    exact integral_map_equiv e f
  simpa only [← heq, W, f] using h



/-- A continuous Sobolev function supplies its own central line increments. -/
theorem coordinate_central_slab_energy_lower_of_h1
    (n : ℕ) (i : Fin (n + 1)) (L c lam Λ s : ℝ)
    (hL : 0 < L) (hc : 0 ≤ c) (hlam : 0 < lam) (hs : 0 ≤ s)
    {U : Set (PDE.Vec (n + 1))} (hU : PDE.IsOpenBoundedConvexDomain U)
    (a : PDE.CoeffField (n + 1)) (u : PDE.H1Function U)
    (hsub : coordinateCentralSlab n i L ⊆ U)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U)
    (hEll : ∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
      (fun x => Real.exp (s * x i) • a x))
    (hA : ∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x))
    (hcont : Continuous u.toFun)
    (hgap : ∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
      c ≤ 1 - u (centralSlabPoint n i (0, z)) ∧
      u (centralSlabPoint n i (L, z)) = 1) :
    lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ x in coordinateCentralSlab n i L,
      PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x) (u.grad x)) (u.grad x) := by
  apply coordinate_central_slab_energy_lower_of_increments n i L c lam Λ s
    hL hc hlam hs a u hsub hEll hA
  filter_upwards [ae_central_slab_increment_of_h1 hU u i L hL hsub hr hball hcont, hgap]
    with z hinc ⟨hcenter, hface⟩
  exact ⟨hinc, hcenter, hface⟩

end EinsteinFull.Regeneration
