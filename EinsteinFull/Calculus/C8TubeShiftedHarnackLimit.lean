import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinFull.Calculus.C9TubeHarnackEpsilonRemoval
import EinsteinFull.Calculus.C17TubeTimeShiftedLocalMax
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.TimeChange.EuclideanTransport

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- A uniform shifted estimate implies the unshifted weak Harnack estimate. -/
theorem c8_native_unit_weak_harnack_from_shifted_estimate
    (d : ℕ) (κ : ℝ)
    (hshift : ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
        ∀ ε : ℝ, 0 < ε →
          eLpNorm (fun z => u z + ε) (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
          ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z + ε))
            (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)))) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
        (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall 0 (1/2))) ≤
        ENNReal.ofReal C * essInf (fun z : ℝ × Vec d => ENNReal.ofReal (u z))
          (volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2))) := by
  obtain ⟨p, C, hp, hC, hs⟩ := hshift
  refine ⟨p, C, hp, hC, ?_⟩
  intro ρ α hell u G hu hu0
  let μ := volume.restrict (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall (0 : Vec d) (1/2))
  let ν := volume.restrict (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall (0 : Vec d) (1/2))
  let ω := volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)
  have hsub : (Set.Ioo (-3/4 : ℝ) (-1/2) ×ˢ sourceBall (0 : Vec d) (1/2)) ⊆
      (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    constructor
    · constructor <;> linarith [ht.1, ht.2]
    · change euclideanNorm (x - 0) < 1 at ⊢
      change euclideanNorm (x - 0) < (1/2 : ℝ) at hx
      linarith
  have hμ : μ ≤ ω := Measure.restrict_mono hsub le_rfl
  have hm : AEStronglyMeasurable u μ := hu.1.aestronglyMeasurable.mono_measure hμ
  have hn : ∀ᵐ z ∂μ, 0 ≤ u z := ae_mono hμ hu0
  have hreg (n : ℕ) : ∀ᵐ y ∂ν,
      eLpNorm (fun z => u z + (1/(n+1 : ℝ))) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * ENNReal.ofReal (u y + (1/(n+1 : ℝ))) := by
    have he : 0 < (1/(n+1 : ℝ)) := by positivity
    have hb := hs ρ α hell u G hu hu0 _ he
    filter_upwards [ae_essInf_le (μ := ν) (f := fun z => ENNReal.ofReal (u z + (1/(n+1 : ℝ))))] with y hy
    apply hb.trans
    simpa only [mul_comm] using mul_le_mul_left hy (ENNReal.ofReal C)
  have hfinal := c9_harnack_epsilon_removal μ ν u u p C hm hn hreg
  have hbound := le_essInf_of_ae_le _ hfinal
  simpa only [essInf, ENNReal.liminf_const_mul_of_ne_zero_of_ne_top
    (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top] using hbound


/-- A uniform essential bound on a finite cover also bounds the covered set. -/
theorem c8_essSup_le_of_finset_cover {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (A : Set X) (U : Finset I)
    (V : I → Set X) (C : ℝ≥0∞) (hcover : A ⊆ ⋃ i ∈ U, V i)
    (hbound : ∀ i ∈ U, essSup f (μ.restrict (V i)) ≤ C) :
    essSup f (μ.restrict A) ≤ C := by
  have h : ∀ᵐ x ∂μ.restrict (⋃ i ∈ U, V i), f x ≤ C :=
    (ae_restrict_biUnion_finset_iff V U _).2 (by
      intro i hi
      filter_upwards [ae_le_essSup (μ := μ.restrict (V i)) (f := f)] with x hx
      exact hx.trans (hbound i hi))
  exact essSup_le_of_ae_le C (ae_mono (Measure.restrict_mono_set μ hcover) h)

/-- Bounded subsets admit finite internal covers by parabolic cylinders at any positive radius. -/
theorem c8_bounded_parabolic_cover (d : ℕ) (A : Set (ℝ × Vec d))
    (hA : ∀ x ∈ A, ‖x‖ ≤ 1) (r : ℝ) (hr : 0 < r) :
    ∃ U : Finset (ℝ × Vec d), (∀ y ∈ U, y ∈ A) ∧
      ∀ x ∈ A, ∃ y ∈ U, x ∈
        Set.Ioo (y.1 - r ^ 2 / 4) (y.1 + r ^ 2 / 4) ×ˢ sourceBall y.2 (r / 2) := by
  let δ : ℝ := min (r ^ 2 / 4) (r / (2 * ((d : ℝ) + 1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  classical
  have hk : IsCompact (Metric.closedBall (0 : ℝ × Vec d) 1) := isCompact_closedBall 0 1
  obtain ⟨T, _, hfin, hcover⟩ := hk.finite_cover_balls (show 0 < δ / 3 by positivity)
  let P : ℝ × Vec d → Prop := fun y => ∃ x ∈ A, dist x y < δ / 3
  let T' := hfin.toFinset.filter P
  let f : ℝ × Vec d → ℝ × Vec d := fun y => if h : P y then Classical.choose h else y
  have hf (y : ℝ × Vec d) (hy : y ∈ T') : f y ∈ A ∧ dist (f y) y < δ / 3 := by
    have hp : P y := (Finset.mem_filter.mp hy).2
    simpa only [f, dite_eq_left hp] using Classical.choose_spec hp
  let U := T'.image f
  refine ⟨U, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact (hf z hz).1
  · intro x hx
    have hxb : x ∈ Metric.closedBall (0 : ℝ × Vec d) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hA x hx
    have hxc := hcover hxb
    simp only [Set.mem_iUnion] at hxc
    obtain ⟨y, hy, hxy⟩ := hxc
    have hxy' : dist x y < δ / 3 := by simpa only [Metric.mem_ball] using hxy
    have hy' : y ∈ T' := Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hy, ⟨x, hx, hxy'⟩⟩
    refine ⟨f y, Finset.mem_image.mpr ⟨y, hy', rfl⟩, ?_⟩
    have hdist : dist x (f y) < δ := by
      have htri := dist_triangle x y (f y)
      have hfy := (hf y hy').2
      rw [dist_comm y (f y)] at htri
      linarith
    have ht : δ ≤ r ^ 2 / 4 := min_le_left _ _
    have hs : ((d : ℝ) + 1) * δ ≤ r / 2 := by
      have hle : δ ≤ r / (2 * ((d : ℝ) + 1)) := min_le_right _ _
      have hdim : 0 < (d : ℝ) + 1 := by positivity
      have h := mul_le_mul_of_nonneg_left hle hdim.le
      have heq : ((d : ℝ) + 1) * (r / (2 * ((d : ℝ) + 1))) = r / 2 := by
        field_simp
      exact heq ▸ h
    have hd : ‖x - f y‖ < δ := by simpa only [dist_eq_norm] using hdist
    have htime : |x.1 - (f y).1| < δ := by
      have h := (norm_fst_le (x - f y)).trans_lt hd
      simpa only [Prod.fst_sub, Real.norm_eq_abs] using h
    have hspace : ‖x.2 - (f y).2‖ < δ := by
      have h := (norm_snd_le (x - f y)).trans_lt hd
      simpa only [Prod.snd_sub] using h
    have hdim : 0 < (d : ℝ) + 1 := by positivity
    have he := (euclideanNorm_le_dimension_mul_norm (x.2 - (f y).2)).trans_lt
      (mul_lt_mul_of_pos_left hspace hdim)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := (abs_lt.mp htime).1
      linarith
    · have := (abs_lt.mp htime).2
      linarith
    · change euclideanNorm (x.2 - (f y).2) < r / 2
      exact he.trans_le hs

/-- Cylinders of radius proportional to the gap fit between nested parabolic cylinders. -/
theorem c8_nested_parabolic_cylinder_subset (d : ℕ) (a b : ℝ)
    (ha : 1 / 2 ≤ a) (hab : a < b)
    (z : ℝ × Vec d)
    (hz : z ∈ Set.Ioo (-(a ^ 2 / 4)) (a ^ 2 / 4) ×ˢ
      sourceBall (0 : Vec d) (a / 2)) :
    let r : ℝ := (b - a) / 4
    Set.Ioo (z.1 - r ^ 2) (z.1 + r ^ 2) ×ˢ sourceBall z.2 r ⊆
      Set.Ioo (-(b ^ 2 / 4)) (b ^ 2 / 4) ×ˢ sourceBall (0 : Vec d) (b / 2) := by
  dsimp only
  intro x hx
  rcases hz with ⟨⟨ht₁, ht₂⟩, hz⟩
  rcases hx with ⟨⟨hx₁, hx₂⟩, hx⟩
  change euclideanNorm (z.2 - 0) < a / 2 at hz
  change euclideanNorm (x.2 - z.2) < (b - a) / 4 at hx
  have htri := TimeChange.euclideanNorm_add_le (x.2 - z.2) (z.2 - 0)
  have hsum : x.2 - 0 = (x.2 - z.2) + (z.2 - 0) := by abel
  have hgap : ((b - a) / 4) ^ 2 ≤ (b ^ 2 - a ^ 2) / 4 := by nlinarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · change euclideanNorm (x.2 - 0) < b / 2
    rw [hsum]
    linarith

/-- Nested centered cylinders lie in the unit product ball. -/
theorem c8_nested_cylinder_bounded (d : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ z ∈ Set.Ioo (-(a ^ 2 / 4)) (a ^ 2 / 4) ×ˢ
      sourceBall (0 : Vec d) (a / 2), ‖z‖ ≤ 1 := by
  intro z hz
  rcases hz with ⟨⟨ht₁, ht₂⟩, hx⟩
  change euclideanNorm (z.2 - 0) < a / 2 at hx
  simp only [sub_zero] at hx
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hnorm : ‖z.2‖ ≤ euclideanNorm z.2 := by
    have hr : 0 ≤ euclideanNorm z.2 := Real.sqrt_nonneg _
    refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    have hsq : z.2 i ^ 2 ≤ euclideanSq z.2 := by
      unfold euclideanSq dot
      rw [sq]
      exact Finset.single_le_sum (f := fun j => z.2 j * z.2 j)
        (fun j _ => mul_self_nonneg (z.2 j)) (Finset.mem_univ i)
    exact Real.abs_le_sqrt hsq
  rw [norm_prod_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  · linarith

/-- A shifted local maximum estimate in terms of the local L² norm. -/
theorem c8_scaled_local_max_l2_of_unit_bound
 (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C)
 (hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
   IsUniformlyElliptic κ ρ α →
   ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
   IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
   essSup (fun z => ENNReal.ofReal |u z|)
    (volume.restrict (Set.Ioo (-1/4:ℝ) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
   ENNReal.ofReal (C * Real.sqrt
    (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z|^2)))
 (t0 : ℝ) (y : Vec d) (r : ℝ) (hr : 0 < r)
 (ρ : Vec d → ℝ) (α : Vec d → Mat d)
 (hell : IsUniformlyElliptic κ ρ α)
 (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
 (hcal : IsWeightedCaloric ρ α (Set.Ioo (t0-r^2) (t0+r^2)) (sourceBall y r) u G) :
 essSup (fun z => ENNReal.ofReal |u z|)
  (volume.restrict (Set.Ioo (t0-r^2/4) (t0+r^2/4) ×ˢ sourceBall y (r/2))) ≤
 ENNReal.ofReal (C * Real.sqrt ((r^(d+2))⁻¹)) *
   eLpNorm u 2 (volume.restrict (Set.Ioo (t0-r^2) (t0+r^2) ×ˢ sourceBall y r)) := by
  have h := c17_time_shifted_scaled_local_max_of_unit_bound d hd κ C hκ hC
    hunit t0 y r hr ρ α hell u G hcal
  have hreal : (eLpNorm u 2 (volume.restrict
      (Set.Ioo (t0-r^2) (t0+r^2) ×ˢ sourceBall y r))).toReal =
      Real.sqrt (∫ z in Set.Ioo (t0-r^2) (t0+r^2) ×ˢ sourceBall y r, |u z| ^ 2) := by
    rw [hcal.1.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs])
    · simp
  have hn : eLpNorm u 2 (volume.restrict
      (Set.Ioo (t0-r^2) (t0+r^2) ×ˢ sourceBall y r)) =
      ENNReal.ofReal (Real.sqrt
        (∫ z in Set.Ioo (t0-r^2) (t0+r^2) ×ˢ sourceBall y r, |u z| ^ 2)) := by
    rw [← hreal, ENNReal.ofReal_toReal hcal.1.eLpNorm_ne_top]
  calc
    _ ≤ ENNReal.ofReal (C * Real.sqrt ((r^(d+2))⁻¹ *
      ∫ z in Set.Ioo (t0-r^2) (t0+r^2) ×ˢ sourceBall y r, |u z| ^ 2)) := h
    _ = _ := by rw [Real.sqrt_mul (by positivity), ← mul_assoc,
      ENNReal.ofReal_mul (by positivity), ← hn]

end EinsteinFull.Calculus
