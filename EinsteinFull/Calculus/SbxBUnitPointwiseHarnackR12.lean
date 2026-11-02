import EinsteinFull.Calculus.C17TubeParabolicScaling
import EinsteinFull.Calculus.SbxBWeightedLocalMaxR09
import EinsteinFull.Calculus.C8TubeShiftedHarnackLimit
import EinsteinFull.Calculus.C17TubeSmallPowerLocalMax
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- Pointwise bounds on an open set follow from essential bounds and continuity. -/
theorem b_continuous_ess_bounds {d : ℕ} (U : Set (ℝ × Vec d)) (hU : IsOpen U)
    (u : ℝ × Vec d → ℝ) (hu : ContinuousOn u U) (z : ℝ × Vec d) (hz : z ∈ U) :
    essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict U) ≤ ENNReal.ofReal (u z) ∧
    ENNReal.ofReal (u z) ≤ essSup (fun x => ENNReal.ofReal (u x)) (volume.restrict U) := by
  let f : ℝ × Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (u x)
  have hf : ContinuousOn f U := ENNReal.continuous_ofReal.comp_continuousOn hu
  have hl : f =ᵐ[volume.restrict U] fun x => max (essInf f (volume.restrict U)) (f x) := by
    filter_upwards [ae_essInf_le (μ := volume.restrict U) (f := f)] with x hx
    exact (max_eq_right hx).symm
  have hr : f =ᵐ[volume.restrict U] fun x => min (f x) (essSup f (volume.restrict U)) := by
    filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict U) f] with x hx
    exact (min_eq_left hx).symm
  have hleft := Measure.eqOn_open_of_ae_eq hl hU hf
    (continuous_max.comp_continuousOn (continuousOn_const.prodMk hf)) hz
  have hright := Measure.eqOn_open_of_ae_eq hr hU hf
    (continuous_min.comp_continuousOn (hf.prodMk continuousOn_const)) hz
  change essInf f (volume.restrict U) ≤ f z ∧ f z ≤ essSup f (volume.restrict U)
  constructor
  · rw [hleft]; exact le_max_left _ _
  · rw [hright]; exact min_le_right _ _

/-- Separate local maximum and weak Harnack norm estimates imply a pointwise
comparison on an early subcylinder and the late cylinder. -/
theorem b_unit_pointwise_harnack_of_norm_bounds (d : ℕ) (κ p A C : ℝ)
    (hA : 0 < A) (hC : 0 < C)
    (hmax : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      essSup (fun z => ENNReal.ofReal (u z))
        (volume.restrict (Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4))) ≤
      ENNReal.ofReal A * eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))))
    (hweak : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal C * essInf (fun z => ENNReal.ofReal (u z))
        (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)))) :
    ∃ H : ℝ, 0 < H ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ContinuousOn u (Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4)) →
      ContinuousOn u (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)) →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ x ∈ Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4),
      ∀ y ∈ Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2),
        0 ≤ u y → u x ≤ H * u y := by
  refine ⟨A*C, mul_pos hA hC, ?_⟩
  intro ρ α hell u G hcal hc1 hc2 hu x hx y hy hy0
  have hx' := (b_continuous_ess_bounds _ (isOpen_Ioo.prod (c17_isOpen_sourceBall _ _)) u hc1 x hx).2
  have hy' := (b_continuous_ess_bounds _ (isOpen_Ioo.prod (c17_isOpen_sourceBall _ _)) u hc2 y hy).1
  have hbound : ENNReal.ofReal (u x) ≤ ENNReal.ofReal (A*C) * ENNReal.ofReal (u y) := by
   calc
    ENNReal.ofReal (u x) ≤ _ := hx'
    _ ≤ ENNReal.ofReal A * eLpNorm u (ENNReal.ofReal p) _ := hmax ρ α hell u G hcal hu
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal C * ENNReal.ofReal (u y)) :=
      mul_le_mul_right ((hweak ρ α hell u G hcal hu).trans (mul_le_mul_right hy' _)) _
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le]
  rw [← ENNReal.ofReal_mul (mul_pos hA hC).le] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_pos hA hC).le hy0)).mp hbound

/-- Radii for the nested cylinders inside the early Harnack cylinder. -/
@[nolint defsWithUnderscore]
noncomputable def b_harnack_radius (r : ℝ) : ℝ :=
  3/8 + max (1/2) (min 1 r) / 4

/-- Nested cylinders centered at time minus five eighths. -/
@[nolint defsWithUnderscore]
noncomputable def b_harnack_cylinder (d : ℕ) (r : ℝ) : Set (ℝ × Vec d) :=
  let a := b_harnack_radius r
  Set.Ioo (-(5/8) - a^2/4) (-(5/8) + a^2/4) ×ˢ sourceBall 0 (a/2)

lemma b_harnack_radius_bounds (r : ℝ) :
    1/2 ≤ b_harnack_radius r ∧ b_harnack_radius r ≤ 5/8 := by
  dsimp [b_harnack_radius]
  have h₁ : (1/2 : ℝ) ≤ max (1/2) (min 1 r) := le_max_left _ _
  have h₂ : max (1/2 : ℝ) (min 1 r) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  constructor <;> linarith

lemma b_harnack_radius_mono : Monotone b_harnack_radius := by
  intro r s hrs
  dsimp [b_harnack_radius]
  have := max_le_max (le_refl (1/2 : ℝ)) (min_le_min_left 1 hrs)
  linarith

lemma b_harnack_radius_of_mem {r : ℝ} (hr : 1/2 ≤ r) (hr' : r ≤ 1) :
    b_harnack_radius r = 3/8 + r/4 := by
  rw [b_harnack_radius, min_eq_right hr', max_eq_right hr]

lemma b_harnack_cylinder_mono (d : ℕ) : Monotone (b_harnack_cylinder d) := by
  intro r s hrs z hz
  have h := b_harnack_radius_mono hrs
  have h0 := (b_harnack_radius_bounds r).1
  have hsq : (b_harnack_radius r)^2 ≤ (b_harnack_radius s)^2 := by nlinarith
  dsimp [b_harnack_cylinder] at hz ⊢
  rcases hz with ⟨⟨ht₁, ht₂⟩, hx⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · change euclideanNorm (z.2 - 0) < b_harnack_radius s / 2
    change euclideanNorm (z.2 - 0) < b_harnack_radius r / 2 at hx
    linarith

lemma b_harnack_cylinder_measurable (d : ℕ) (r : ℝ) :
    MeasurableSet (b_harnack_cylinder d r) := by
  exact (isOpen_Ioo.prod (c17_isOpen_sourceBall _ _)).measurableSet

lemma b_harnack_cylinder_half (d : ℕ) :
    b_harnack_cylinder d (1/2) =
      Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4) := by
  norm_num [b_harnack_cylinder, b_harnack_radius]

lemma b_harnack_cylinder_one_subset (d : ℕ) :
    b_harnack_cylinder d 1 ⊆
      Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2) := by
  intro z hz
  norm_num [b_harnack_cylinder, b_harnack_radius] at hz
  rcases hz with ⟨⟨ht₁, ht₂⟩, hx⟩
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  change euclideanNorm (z.2 - 0) < (1/2 : ℝ)
  change euclideanNorm (z.2 - 0) < (5/16 : ℝ) at hx
  linarith

/-- A small cylinder around a point of a nested cylinder lies in the next one. -/
lemma b_harnack_cylinder_nested (d : ℕ) (r s : ℝ)
    (hr : 1/2 ≤ r) (hrs : r < s) (hs : s ≤ 1)
    (z : ℝ × Vec d) (hz : z ∈ b_harnack_cylinder d r) :
    let δ := (s-r)/16
    Set.Ioo (z.1-δ^2) (z.1+δ^2) ×ˢ sourceBall z.2 δ ⊆
      b_harnack_cylinder d s := by
  dsimp only
  intro x hx
  have hs' : 1/2 ≤ s := le_trans hr hrs.le
  have hr' : r ≤ 1 := le_trans hrs.le hs
  have hgap : (s-r)/16 = (b_harnack_radius s - b_harnack_radius r)/4 := by
    rw [b_harnack_radius_of_mem hr hr', b_harnack_radius_of_mem hs' hs]
    ring
  have ha : 0 ≤ b_harnack_radius r := (b_harnack_radius_bounds r).1.trans' (by norm_num)
  have hab : b_harnack_radius r ≤ b_harnack_radius s := b_harnack_radius_mono hrs.le
  have hsq : ((s-r)/16)^2 ≤
      ((b_harnack_radius s)^2 - (b_harnack_radius r)^2)/4 := by
    rw [hgap]
    have hm := mul_nonneg (sub_nonneg.mpr hab)
      (show 0 ≤ 3*b_harnack_radius s + 5*b_harnack_radius r by linarith)
    nlinarith
  rcases hz with ⟨⟨ht₁, ht₂⟩, hz⟩
  rcases hx with ⟨⟨hx₁, hx₂⟩, hx⟩
  change euclideanNorm (z.2 - 0) < b_harnack_radius r / 2 at hz
  change euclideanNorm (x.2 - z.2) < (s-r)/16 at hx
  have htri := TimeChange.euclideanNorm_add_le (x.2 - z.2) (z.2 - 0)
  have heq : x.2 - 0 = (x.2 - z.2) + (z.2 - 0) := by abel
  change (-(5/8) - (b_harnack_radius s)^2/4 < x.1 ∧
    x.1 < -(5/8) + (b_harnack_radius s)^2/4) ∧
    euclideanNorm (x.2 - 0) < b_harnack_radius s/2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · rw [heq]
    rw [hgap] at hx
    linarith

/-- Every nested cylinder is contained in the unit product ball. -/
lemma b_harnack_cylinder_bounded (d : ℕ) (r : ℝ) :
    ∀ z ∈ b_harnack_cylinder d r, ‖z‖ ≤ 1 := by
  intro z hz
  have ha := b_harnack_radius_bounds r
  rcases hz with ⟨⟨ht₁, ht₂⟩, hx⟩
  change euclideanNorm (z.2 - 0) < b_harnack_radius r / 2 at hx
  simp only [sub_zero] at hx
  have hsq : (b_harnack_radius r)^2 ≤ 1 := by nlinarith
  have hnorm : ‖z.2‖ ≤ euclideanNorm z.2 := by
    have hn : 0 ≤ euclideanNorm z.2 := Real.sqrt_nonneg _
    refine (pi_norm_le_iff_of_nonneg hn).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    have hi : z.2 i ^ 2 ≤ euclideanSq z.2 := by
      unfold euclideanSq dot
      rw [sq]
      exact Finset.single_le_sum (f := fun j => z.2 j * z.2 j)
        (fun j _ => mul_self_nonneg (z.2 j)) (Finset.mem_univ i)
    exact Real.abs_le_sqrt hi
  rw [norm_prod_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  · linarith

/-- The weighted unit local maximum estimate in integral form. -/
theorem b_weighted_unit_L2_local_max_integral
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      essSup (fun z => ENNReal.ofReal |u z|)
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (C * Real.sqrt
        (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z| ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := b_weighted_unit_L2_local_max d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal
  have hreal : (eLpNorm u 2
      (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))).toReal =
      Real.sqrt (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z| ^ 2) := by
    rw [hcal.1.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs])
    · simp
  have hn : eLpNorm u 2 (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) =
      ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z| ^ 2)) := by
    rw [← hreal, ENNReal.ofReal_toReal hcal.1.eLpNorm_ne_top]
  have hsup : essSup (fun z => ENNReal.ofReal |u z|)
      (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      eLpNorm u ⊤ (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) := by
    simpa only [eLpNormEssSup_eq_essSup_enorm, Real.enorm_eq_ofReal_abs] using
      (eLpNormEssSup_le_eLpNorm_top (f := u)
        (μ := volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))))
  calc
    _ ≤ ENNReal.ofReal C * eLpNorm u 2
        (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := hsup.trans (hbound ρ α hell u G hcal)
    _ = _ := by rw [hn, ← ENNReal.ofReal_mul hC.le]

lemma b_harnack_cylinder_subset_unit (d : ℕ) (r : ℝ) :
    b_harnack_cylinder d r ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 := by
  intro z hz
  have hs : b_harnack_radius r ≤ 5/8 := (b_harnack_radius_bounds r).2
  have h0 : 0 ≤ b_harnack_radius r := by have := (b_harnack_radius_bounds r).1; linarith
  have hsq : (b_harnack_radius r)^2 ≤ 1 := by nlinarith
  rcases hz with ⟨⟨ht₁, ht₂⟩, hx⟩
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  change euclideanNorm (z.2 - 0) < (1 : ℝ)
  change euclideanNorm (z.2 - 0) < b_harnack_radius r / 2 at hx
  linarith

/-- The nested weighted local maximum gain with its explicit scaling factor. -/
theorem b_harnack_nested_L2_gain (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ r s : ℝ, 1/2 ≤ r → r < s → s ≤ 1 →
      eLpNorm u ⊤ (volume.restrict (b_harnack_cylinder d r)) ≤
        ENNReal.ofReal (C * Real.sqrt ((((s-r)/16)^(d+2))⁻¹)) *
          eLpNorm u 2 (volume.restrict (b_harnack_cylinder d s)) := by
  obtain ⟨C, hC, hunit⟩ := b_weighted_unit_L2_local_max_integral d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal r s hr hrs hs
  let δ : ℝ := (s-r)/16
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨U, hU, hcover⟩ := c8_bounded_parabolic_cover d
    (b_harnack_cylinder d r) (b_harnack_cylinder_bounded d r) δ hδ
  let V : (ℝ × Vec d) → Set (ℝ × Vec d) := fun z =>
    Set.Ioo (z.1-δ^2/4) (z.1+δ^2/4) ×ˢ sourceBall z.2 (δ/2)
  let W : (ℝ × Vec d) → Set (ℝ × Vec d) := fun z =>
    Set.Ioo (z.1-δ^2) (z.1+δ^2) ×ˢ sourceBall z.2 δ
  have hcover' : b_harnack_cylinder d r ⊆ ⋃ z ∈ U, V z := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hcover x hx
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hzx⟩⟩
  have hbound : ∀ z ∈ U, essSup (fun x => ENNReal.ofReal |u x|)
      (volume.restrict (V z)) ≤
      ENNReal.ofReal (C * Real.sqrt ((δ^(d+2))⁻¹)) *
        eLpNorm u 2 (volume.restrict (b_harnack_cylinder d s)) := by
    intro z hz
    have hw : W z ⊆ b_harnack_cylinder d s :=
      b_harnack_cylinder_nested d r s hr hrs hs z (hU z hz)
    have hwunit := hw.trans (b_harnack_cylinder_subset_unit d s)
    have ht : Set.Ioo (z.1-δ^2) (z.1+δ^2) ⊆ Set.Ioo (-1 : ℝ) 1 := by
      intro t ht
      have hcenter : z.2 ∈ sourceBall z.2 δ := by
        change euclideanNorm (z.2 - z.2) < δ
        simpa [euclideanNorm, euclideanSq, dot] using hδ
      exact (hwunit (show (t, z.2) ∈ W z from ⟨ht, hcenter⟩)).1
    have hx : sourceBall z.2 δ ⊆ sourceBall (0 : Vec d) 1 := by
      intro x hx
      have hcenter : z.1 ∈ Set.Ioo (z.1-δ^2) (z.1+δ^2) := by
        have hp : 0 < δ^2 := sq_pos_of_pos hδ
        constructor <;> linarith
      exact (hwunit (show (z.1, x) ∈ W z from ⟨hcenter, hx⟩)).2
    have hlocal := c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
      (c17_isOpen_sourceBall _ _).measurableSet ht hx hcal
    calc
      _ ≤ ENNReal.ofReal (C * Real.sqrt ((δ^(d+2))⁻¹)) *
          eLpNorm u 2 (volume.restrict (W z)) :=
        c8_scaled_local_max_l2_of_unit_bound d hd κ C hκ hC (by simpa only [neg_div] using hunit)
          z.1 z.2 δ hδ ρ α hell u G hlocal
      _ ≤ _ := mul_le_mul_right (eLpNorm_mono_measure u
        (Measure.restrict_mono_set volume hw)) _
  have hsup := c8_essSup_le_of_finset_cover volume (fun x => ENNReal.ofReal |u x|)
    (b_harnack_cylinder d r) U V _ hcover' hbound
  have hm : AEStronglyMeasurable u (volume.restrict (b_harnack_cylinder d r)) :=
    hcal.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume
      (b_harnack_cylinder_subset_unit d r))
  rw [eLpNorm_exponent_top hm, eLpNormEssSup_eq_essSup_enorm]
  simpa only [Real.enorm_eq_ofReal_abs] using hsup

/-- Polynomial form of the nested weighted local maximum gain. -/
theorem b_harnack_nested_polynomial_L2_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ A m : ℝ, 0 < A ∧ 0 < m ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ r s : ℝ, 1/2 ≤ r → r < s → s ≤ 1 →
      eLpNorm u ⊤ (volume.restrict (b_harnack_cylinder d r)) ≤
        ENNReal.ofReal (A * Real.rpow (s-r) (-m)) *
          eLpNorm u 2 (volume.restrict (b_harnack_cylinder d s)) := by
  obtain ⟨C, hC, hgain⟩ := b_harnack_nested_L2_gain d hd κ hκ
  refine ⟨C * (16:ℝ)^(d+2), ((d+2 : ℕ) : ℝ), by positivity, by positivity, ?_⟩
  intro ρ α hell u G hcal r s hr hrs hs
  have hδ : 0 < (s-r)/16 := by linarith
  have hδ1 : (s-r)/16 ≤ 1 := by linarith
  have hp : 0 < ((s-r)/16)^(d+2) := pow_pos hδ _
  have hp1 : ((s-r)/16)^(d+2) ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hsqrt : Real.sqrt ((((s-r)/16)^(d+2))⁻¹) ≤ (((s-r)/16)^(d+2))⁻¹ :=
    Real.sqrt_le_self_iff.mpr (Or.inr ((one_le_inv₀ hp).mpr hp1))
  have hid : (((s-r)/16)^(d+2))⁻¹ = (16:ℝ)^(d+2) *
      Real.rpow (s-r) (-((d+2 : ℕ) : ℝ)) := by
    change (((s-r)/16)^(d+2))⁻¹ = (16:ℝ)^(d+2) * (s-r) ^ (-((d+2 : ℕ) : ℝ))
    rw [Real.rpow_neg (by linarith : 0 ≤ s-r) (((d+2 : ℕ) : ℝ)), Real.rpow_natCast, div_pow, inv_div]
    ring
  calc
    _ ≤ ENNReal.ofReal (C * Real.sqrt ((((s-r)/16)^(d+2))⁻¹)) *
      eLpNorm u 2 (volume.restrict (b_harnack_cylinder d s)) :=
      hgain ρ α hell u G hcal r s hr hrs hs
    _ ≤ _ := by
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      rw [mul_assoc, ← hid]
      nlinarith

/-- The early local maximum bound at every positive exponent below two. -/
theorem b_unit_local_max_small_power (d : ℕ) (hd : 2 ≤ d)
    (κ p : ℝ) (hκ : 0 < κ) (hp : 0 < p) (hp2 : p < 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      essSup (fun z => ENNReal.ofReal (u z))
        (volume.restrict (Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4))) ≤
      ENNReal.ofReal A * eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) := by
  obtain ⟨B, m, hB, hm, hgain⟩ := b_harnack_nested_polynomial_L2_gain d hd κ hκ
  obtain ⟨A, hA, habs⟩ := c17_small_power_local_max_of_L2_gain p B m hp hp2 hB hm
  refine ⟨A, hA, ?_⟩
  intro ρ α hell u G hcal
  have hu : MemLp u 2 (volume.restrict (b_harnack_cylinder d 1)) :=
    hcal.1.mono_measure (Measure.restrict_mono_set volume (b_harnack_cylinder_subset_unit d 1))
  have hgain' := hgain ρ α hell u G hcal
  have hsmall := habs volume (b_harnack_cylinder d) u
    (b_harnack_cylinder_measurable d) (b_harnack_cylinder_mono d) hu hgain'
  have hsup : essSup (fun z => ENNReal.ofReal (u z))
      (volume.restrict (b_harnack_cylinder d (1/2))) ≤
      eLpNorm u ⊤ (volume.restrict (b_harnack_cylinder d (1/2))) := by
    calc
      _ ≤ essSup (fun z => ENNReal.ofReal |u z|)
          (volume.restrict (b_harnack_cylinder d (1/2))) :=
        essSup_mono_ae (Filter.Eventually.of_forall fun z => ENNReal.ofReal_le_ofReal (le_abs_self _))
      _ ≤ _ := by
        simpa only [eLpNormEssSup_eq_essSup_enorm, Real.enorm_eq_ofReal_abs] using
          (eLpNormEssSup_le_eLpNorm_top (f := u)
            (μ := volume.restrict (b_harnack_cylinder d (1/2))))
  rw [← b_harnack_cylinder_half d]
  calc
    _ ≤ _ := hsup
    _ ≤ ENNReal.ofReal A * eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (b_harnack_cylinder d 1)) := hsmall
    _ ≤ _ := mul_le_mul_right
      (eLpNorm_mono_measure u (Measure.restrict_mono_set volume
        (b_harnack_cylinder_one_subset d))) _

/-- The early weighted local maximum bound at every positive exponent. -/
theorem b_unit_local_max_positive_power (d : ℕ) (hd : 2 ≤ d)
    (κ p : ℝ) (hκ : 0 < κ) (hp : 0 < p) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      essSup (fun z => ENNReal.ofReal (u z))
        (volume.restrict (Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4))) ≤
      ENNReal.ofReal A * eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) := by
  by_cases hp2 : p < 2
  · exact b_unit_local_max_small_power d hd κ p hκ hp hp2
  · have hp1 : 1 ≤ p := by linarith
    obtain ⟨A, hA, hmax⟩ := b_unit_local_max_small_power d hd κ 1 hκ (by norm_num) (by norm_num)
    let μ : Measure (ℝ × Vec d) := volume.restrict
      (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))
    let e : ℝ := 1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal
    let V : ℝ≥0∞ := μ Set.univ ^ e
    have he : 0 ≤ e := by
      dsimp [e]
      rw [ENNReal.toReal_ofReal hp.le]
      have hi : p⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr hp1
      simp only [one_div]
      linarith
    haveI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure (-3/4) (-1/2) (1/2) 0
    have hV : V ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg he (measure_ne_top μ Set.univ)).ne
    let B : ℝ := V.toReal + 1
    have hB : 0 < B := by dsimp [B]; have := ENNReal.toReal_nonneg (a := V); linarith
    have hVB : V ≤ ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_toReal hV]
      apply ENNReal.ofReal_le_ofReal
      dsimp [B]
      linarith
    refine ⟨A*B, mul_pos hA hB, ?_⟩
    intro ρ α hell u G hcal
    have hsub : (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall (0 : Vec d) (1/2)) ⊆
        (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) := by
      intro z hz
      rcases hz with ⟨⟨ht₁, ht₂⟩, hx⟩
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      change euclideanNorm (z.2 - 0) < (1 : ℝ)
      change euclideanNorm (z.2 - 0) < (1/2 : ℝ) at hx
      linarith
    have hmeas : AEStronglyMeasurable u μ := hcal.1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hsub)
    have hpq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp1
    have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hmeas
    have hcompare' : eLpNorm u 1 μ ≤ eLpNorm u (ENNReal.ofReal p) μ * V := hcompare
    calc
      _ ≤ ENNReal.ofReal A * eLpNorm u 1 μ := by
        simpa only [ENNReal.ofReal_one] using hmax ρ α hell u G hcal
      _ ≤ ENNReal.ofReal A * (eLpNorm u (ENNReal.ofReal p) μ * V) :=
        mul_le_mul_right hcompare' _
      _ ≤ ENNReal.ofReal A * (eLpNorm u (ENNReal.ofReal p) μ * ENNReal.ofReal B) :=
        mul_le_mul_right (mul_le_mul_right hVB _) _
      _ = _ := by rw [ENNReal.ofReal_mul hA.le]; ring

/-- A unit weak Harnack norm estimate yields pointwise Harnack comparison. -/
theorem b_unit_pointwise_harnack_of_weak_harnack (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ)
    (hweak : ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal C * essInf (fun z => ENNReal.ofReal (u z))
        (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)))) :
    ∃ H : ℝ, 0 < H ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ContinuousOn u (Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4)) →
      ContinuousOn u (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)) →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ x ∈ Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4),
      ∀ y ∈ Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2),
        0 ≤ u y → u x ≤ H * u y := by
  obtain ⟨p, C, hp, hC, hweak⟩ := hweak
  obtain ⟨A, hA, hmax⟩ := b_unit_local_max_positive_power d hd κ p hκ hp
  apply b_unit_pointwise_harnack_of_norm_bounds d κ p A C hA hC ?_ hweak
  intro ρ α hell u G hcal _
  exact hmax ρ α hell u G hcal

end EinsteinFull.Calculus

