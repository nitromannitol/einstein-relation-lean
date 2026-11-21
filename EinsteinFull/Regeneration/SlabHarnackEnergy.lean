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

/-- A fixed transverse coordinate determines a continuous force-coordinate line. -/
theorem continuous_centralSlabPoint (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℝ) :
    Continuous (fun t => centralSlabPoint n i (t, z)) := by
  apply continuous_pi
  intro j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · have hi : (fun t => centralSlabPoint n i (t, z) i) = id :=
      funext fun t => (centralSlabPoint_coord n i t z).1
    rw [hi]
    exact continuous_id
  · have hk : (fun t => centralSlabPoint n i (t, z) (i.succAbove k)) =
        fun _ => z k := funext fun t => (centralSlabPoint_coord n i t z).2 k
    rw [hk]
    exact continuous_const

/-- For large enough sides, the source slab box contains every comparison ball. -/
theorem central_comparison_ball_subset_slab_box (n : ℕ) (i : Fin (n + 1))
    (s L : ℝ) (z : Fin n → ℝ)
    (hz : z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))
    (hL : Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)) + 1 ≤ L)
    (hT : Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)) + 1 ≤
      Real.exp (s * L / (n + 1))) :
    PDE.euclideanBall
      ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
      (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ coordinateSlabBox n i s L := by
  let R : ℝ := Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))
  let center : PDE.Vec (n + 1) :=
    (1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z))
  have hR : 0 < R := by dsimp [R]; positivity
  have hcenter (j : Fin (n + 1)) : |center j| ≤ 1 / 2 := by
    have hzj := centralSlabPoint_abs_le_one n i z hz j
    dsimp only [center, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.zero_apply, zero_add]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp only [zero_add]
    nlinarith
  intro y hy
  have hyR := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hy
  have hycoord (j : Fin (n + 1)) : |y j| < R + 1 := by
    have h := (PDE.abs_apply_le_vecEuclideanNorm (y - center) j).trans_lt hyR
    have hc := abs_le.mp (hcenter j)
    have ht := abs_lt.mp h
    simp only [Pi.sub_apply] at ht
    apply abs_lt.mpr
    constructor <;> linarith
  change (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i y) ∈
    Icc (-L) L ×ˢ Icc (fun _ => -Real.exp (s * L / (n + 1)))
      (fun _ => Real.exp (s * L / (n + 1)))
  constructor
  · have hi := abs_lt.mp (hycoord i)
    change -L ≤ y i ∧ y i ≤ L
    constructor <;> linarith
  · constructor
    · intro j
      have hj := abs_lt.mp (hycoord (i.succAbove j))
      change -Real.exp (s * L / (n + 1)) ≤ y (i.succAbove j)
      linarith
    · intro j
      have hj := abs_lt.mp (hycoord (i.succAbove j))
      change y (i.succAbove j) ≤ Real.exp (s * L / (n + 1))
      linarith

/-- Every fixed positive force eventually makes both slab sides large enough. -/
theorem exists_large_slab_sides (n : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀,
      Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)) + 1 ≤ L ∧
      Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)) + 1 ≤
        Real.exp (s * L / (n + 1)) := by
  let R := Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))
  let d : ℝ := n + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  refine ⟨max (R + 1) ((R + 1) * d / s), ?_, ?_⟩
  · exact (by positivity : 0 < R + 1) |>.trans_le (le_max_left _ _)
  · intro L hL
    have hL1 : R + 1 ≤ L := (le_max_left _ _).trans hL
    have hL2 : (R + 1) * d / s ≤ L := (le_max_right _ _).trans hL
    have hmul : (R + 1) * d ≤ L * s := (div_le_iff₀ hs).1 hL2
    have hr : R + 1 ≤ s * L / d := by
      apply (le_div_iff₀ hd).2
      nlinarith
    have hexp := Real.add_one_le_exp (s * L / d)
    constructor
    · exact hL1
    · change R + 1 ≤ Real.exp (s * L / d)
      linarith

/-- The central half-slab lies in the source slab box when the transverse side is at least one. -/
theorem coordinateCentralSlab_subset_slabBox (n : ℕ) (i : Fin (n + 1)) (s L : ℝ)
    (hL : 0 ≤ L) (hT : 1 ≤ Real.exp (s * L / (n + 1))) :
    coordinateCentralSlab n i L ⊆ coordinateSlabBox n i s L := by
  intro x hx
  change (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x) ∈
    Ioc 0 L ×ˢ Icc (fun _ => (-1 : ℝ)) (fun _ => 1) at hx
  change (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x) ∈
    Icc (-L) L ×ˢ Icc (fun _ => -Real.exp (s * L / (n + 1)))
      (fun _ => Real.exp (s * L / (n + 1)))
  refine ⟨⟨?_, hx.1.2⟩, ?_⟩
  · linarith [hx.1.1]
  · constructor
    · intro j
      have h := hx.2.1 j
      dsimp only at h ⊢
      linarith
    · intro j
      have h := hx.2.2 j
      dsimp only at h ⊢
      linarith

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
  filter_upwards [ae_restrict_mem measurableSet_Icc, hslice] with z hz ⟨hweak, hface⟩
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
  exact ⟨(hcont.comp (continuous_centralSlabPoint n i z)).continuousOn, hweak, hgap, hface⟩

/-- A small center value forces the source full-box energy lower bound at large scales. -/
theorem exists_slab_box_energy_lower_of_harnack
    (n : ℕ) (lam Λ s : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ) (hs : 0 < s) :
    ∃ c L₀ : ℝ, 0 < c ∧ 0 < L₀ ∧ ∀ (i : Fin (n + 1)) (L : ℝ), L₀ ≤ L →
      ∀ {U : Set (PDE.Vec (n + 1))} (a : PDE.CoeffField (n + 1)) (u : PDE.H1Function U),
      IsOpen U → coordinateSlabBox n i s L ⊆ U →
      (∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
        (fun x => Real.exp (s * x i) • a x)) →
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → u 0 < 2 / 3 →
      (∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
        PDE.HasWeakDerivOnIoo 0 L (fun t => u (centralSlabPoint n i (t, z)))
          (fun t => u.grad (centralSlabPoint n i (t, z)) i) ∧
        u (centralSlabPoint n i (L, z)) = 1) →
      lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ x in coordinateSlabBox n i s L,
        PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x) (u.grad x)) (u.grad x) := by
  obtain ⟨c, hc, henergy⟩ :=
    exists_central_slab_energy_lower_of_harnack n lam Λ s hlam hΛ hs
  obtain ⟨L₀, hL₀, hsides⟩ := exists_large_slab_sides n s hs
  refine ⟨c, L₀, hc, hL₀, ?_⟩
  intro i L hL U a u hU hbox hEll hmeas hA hsol hcont hupper hsmall hslice
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
  have hlow := henergy i L hLpos a u hU (hcentral.trans hbox) hballs hEll
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
