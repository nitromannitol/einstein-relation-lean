import EinsteinFull.Calculus.C11TubeWeightedLocalMax
import EinsteinFull.Calculus.C17TubeNativeConcentricInverseGain
import EinsteinFull.Calculus.C18TubeCaloricTimeTranslation

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- A unit-cylinder solution restricts to each actual dyadic cylinder used by
    the signed iteration. -/
theorem c9_weighted_caloric_dyadic_restrict {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (n : ℕ) :
    IsWeightedCaloric ρ α
      (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)))
      (sourceBall 0 (1 / 2 + 1 / (2 * (2 : ℝ) ^ n))) u G := by
  have hz : 0 < (2 : ℝ) ^ n := by positivity
  have ht : (0 : ℝ) ∈ Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
      (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) := by
    have hp : 0 < 3 / (4 * (2 : ℝ) ^ n) := by positivity
    constructor <;> linarith
  have hx : (0 : Vec d) ∈ sourceBall 0 (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)) := by
    change euclideanNorm ((0 : Vec d) - 0) < _
    simp only [sub_self]
    have hzero : euclideanNorm (0 : Vec d) = 0 := by
      simp [euclideanNorm, euclideanSq, dot]
    rw [hzero]
    positivity
  have hsub := (c11_moser_dyadic_cylinder_containment d n).2
  apply c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet ?_ ?_ hcal
  · intro t ht'
    exact (hsub (show (t, (0 : Vec d)) ∈ _ from ⟨ht', hx⟩)).1
  · intro x hx'
    exact (hsub (show ((0 : ℝ), x) ∈ _ from ⟨ht, hx'⟩)).2

/-- A dyadic spatial gap contains a parabolic cylinder whose time gap also
    fits in the next larger dyadic cylinder. -/
theorem c9_dyadic_parabolic_radius_bounds (n : ℕ) :
    let z : ℝ := (2 : ℝ) ^ n
    let r : ℝ := 1 / (8 * z)
    0 < r ∧ r < 1 / (4 * z) ∧ r ^ 2 < 3 / (8 * z) := by
  dsimp only
  have hz : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hzpos : 0 < (2 : ℝ) ^ n := by positivity
  have hr : 0 < 1 / (8 * (2 : ℝ) ^ n) := by positivity
  have hrle : 1 / (8 * (2 : ℝ) ^ n) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity : 0 < 8 * (2 : ℝ) ^ n)]
    nlinarith
  have hs : 1 / (4 * (2 : ℝ) ^ n) = 2 * (1 / (8 * (2 : ℝ) ^ n)) := by
    field_simp <;> norm_num
  have ht : 3 / (8 * (2 : ℝ) ^ n) = 3 * (1 / (8 * (2 : ℝ) ^ n)) := by
    field_simp
  rw [hs, ht]
  constructor
  · exact hr
  constructor <;> nlinarith

/-- Every point of the inner dyadic cylinder is the centre of a parabolic
    cylinder contained in the preceding dyadic cylinder. -/
theorem c9_dyadic_local_cylinder_containment (d n : ℕ) (t : ℝ) (y : Vec d)
    (hinner : (t, y) ∈
      Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
      sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n))) :
    let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
    Set.Ioo (t - r ^ 2) (t + r ^ 2) ×ˢ sourceBall y r ⊆
      Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
      sourceBall 0 (1 / 2 + 1 / (2 * (2 : ℝ) ^ n)) := by
  dsimp only
  rcases hinner with ⟨⟨ht₁, ht₂⟩, hy⟩
  intro ⟨s, x⟩ ⟨⟨hs₁, hs₂⟩, hx⟩
  change euclideanNorm (y - 0) < _ at hy
  change euclideanNorm (x - y) < _ at hx
  have ⟨_, hr, htime⟩ := c9_dyadic_parabolic_radius_bounds n
  have hsum : x - 0 = (x - y) + (y - 0) := by abel
  have htri := TimeChange.euclideanNorm_add_le (x - y) (y - 0)
  have hgap : 1 / (2 * (2 : ℝ) ^ n) =
      2 * (1 / (4 * (2 : ℝ) ^ n)) := by field_simp <;> norm_num
  have htgap : 3 / (4 * (2 : ℝ) ^ n) =
      2 * (3 / (8 * (2 : ℝ) ^ n)) := by field_simp <;> norm_num
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [htgap]; linarith
  · rw [htgap]; linarith
  · change euclideanNorm (x - 0) < _
    rw [hsum, hgap]
    linarith

/-- A unit-cylinder solution is caloric on the parabolic cylinder centred at
    each point of the inner dyadic cylinder. -/
theorem c9_weighted_caloric_dyadic_local {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (n : ℕ) (t : ℝ) (y : Vec d)
    (hinner : (t, y) ∈
      Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
      sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n))) :
    let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
    IsWeightedCaloric ρ α (Set.Ioo (t - r ^ 2) (t + r ^ 2)) (sourceBall y r) u G := by
  dsimp only
  have hr : 0 < 1 / (8 * (2 : ℝ) ^ n) := (c9_dyadic_parabolic_radius_bounds n).1
  have ht : t ∈ Set.Ioo (t - (1 / (8 * (2 : ℝ) ^ n)) ^ 2)
      (t + (1 / (8 * (2 : ℝ) ^ n)) ^ 2) := by
    have hp : 0 < (1 / (8 * (2 : ℝ) ^ n)) ^ 2 := sq_pos_of_pos hr
    constructor <;> linarith
  have hy : y ∈ sourceBall y (1 / (8 * (2 : ℝ) ^ n)) := by
    change euclideanNorm (y - y) < _
    simp only [sub_self]
    have hzero : euclideanNorm (0 : Vec d) = 0 := by
      simp [euclideanNorm, euclideanSq, dot]
    rw [hzero]
    exact hr
  have hsub := c9_dyadic_local_cylinder_containment d n t y hinner
  apply c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) _).measurableSet ?_ ?_
    (c9_weighted_caloric_dyadic_restrict hcal n)
  · intro s hs
    exact (hsub (show (s, y) ∈ _ from ⟨hs, hy⟩)).1
  · intro x hx
    exact (hsub (show (t, x) ∈ _ from ⟨ht, hx⟩)).2

/-- Both signs of a unit-cylinder solution remain caloric on each dyadic
    cylinder, with the corresponding signed gradient. -/
theorem c9_weighted_caloric_dyadic_signed {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (n : ℕ) :
    let I := Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
      (1 / 4 + 3 / (4 * (2 : ℝ) ^ n))
    let U := sourceBall (0 : Vec d) (1 / 2 + 1 / (2 * (2 : ℝ) ^ n))
    IsWeightedCaloric ρ α I U u G ∧
      IsWeightedCaloric ρ α I U (fun z => -u z) (fun z => -G z) := by
  have h := c9_weighted_caloric_dyadic_restrict hcal n
  exact ⟨h, c11_weighted_caloric_neg h⟩

/-- The full signed unit gain applies, with its original uniform constant, to
    every parabolically normalized weighted-caloric solution. -/
theorem c9_normalized_signed_unit_gain
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t₀ : ℝ) (y : Vec d) (r : ℝ), 0 < r →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (t₀-r^2) (t₀+r^2)) (sourceBall y r) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm (fun z => u (t₀+r^2*z.1, y+r • z.2))
        (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
      eLpNorm (fun z => u (t₀+r^2*z.1, y+r • z.2)) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := by
  obtain ⟨C, hC, hunit⟩ := hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro t₀ y r hr ρ α hell u G hcal p hp
  have he : IsUniformlyElliptic κ (fun x => ρ (y+r • x)) (fun x => α (y+r • x)) :=
    ⟨hell.1.comp (c17_spatial_affine_embedding y hr).measurable,
      hell.2.1.comp (c17_spatial_affine_embedding y hr).measurable, fun x => hell.2.2 _⟩
  exact hunit _ _ he _ _ (c17_weighted_caloric_parabolic_rescale t₀ y hr ρ α u G hcal) p hp

/-- The signed unit gain applies at every centre of an inner dyadic cylinder,
    with a constant chosen before the fields and the dyadic index. -/
theorem c9_dyadic_local_normalized_signed_gain
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ (n : ℕ) (t : ℝ) (y : Vec d),
      (t, y) ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)) →
      ∀ p : ℝ, 2 ≤ p →
      let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
      eLpNorm (fun z => u (t+r^2*z.1, y+r • z.2))
        (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
      eLpNorm (fun z => u (t+r^2*z.1, y+r • z.2)) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := by
  obtain ⟨C, hC, hgain⟩ := c9_normalized_signed_unit_gain d κ hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal n t y hinner p hp
  exact hgain t y (1 / (8 * (2 : ℝ) ^ n))
    (c9_dyadic_parabolic_radius_bounds n).1 ρ α hell u G
    (c9_weighted_caloric_dyadic_local hcal n t y hinner) p hp

/-- The signed unit gain transfers to centered physical cylinders with the
    exact Jacobian factors on both norms. -/
theorem c9_centered_signed_gain_with_jacobian
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : Vec d) (r : ℝ), 0 < r →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-r^2) (r^2)) (sourceBall y r) u G →
      ∀ p : ℝ, 2 ≤ p →
      let J : ℝ≥0∞ := ENNReal.ofReal |(r^2)⁻¹| *
        ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
      J ^ (1 / ENNReal.ofReal (p*((d:ℝ)+2)/d)).toReal *
        eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
          (volume.restrict (Set.Ioo (-(r^2)/4) (r^2/4) ×ˢ sourceBall y (r/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        (J ^ (1 / ENNReal.ofReal p).toReal *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (-r^2) (r^2) ×ˢ sourceBall y r))) := by
  obtain ⟨C, hC, hnorm⟩ := c9_normalized_signed_unit_gain d κ hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro y r hr ρ α hell u G hcal p hp
  have h := hnorm 0 y r hr ρ α hell u G (by simpa using hcal) p hp
  simp only [zero_add] at h
  have hs := c17_small_cylinder_eLpNorm_rescale y hr (ENNReal.ofReal (p*((d:ℝ)+2)/d)) u
  have hl := c17_parabolic_eLpNorm_preimage y hr
    (Set.Ioo (-r^2) (r^2) ×ˢ sourceBall y r)
    (measurableSet_Ioo.prod (c17_isOpen_sourceBall y r).measurableSet)
    (ENNReal.ofReal p) u
  dsimp only at hl
  rw [c17_concentric_cylinder_preimage y hr r] at hl
  simp only [div_self hr.ne', one_pow] at hl
  dsimp only
  rw [← hs, ← hl]
  simpa only [Function.comp_def, neg_div] using h

/-- Translation of time preserves the Lp norm on a shifted cylinder. -/
theorem c9_time_shifted_cylinder_eLpNorm {d : ℕ} (t a b : ℝ)
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : ℝ × Vec d → ℝ) :
    eLpNorm (fun z => f (t + z.1, z.2)) p
      (volume.restrict (Set.Ioo a b ×ˢ U)) =
    eLpNorm f p (volume.restrict (Set.Ioo (t+a) (t+b) ×ˢ U)) := by
  have he : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1+t, z.2)) := by
    convert (Homeomorph.addRight (t, (0 : Vec d))).measurableEmbedding using 1
    funext z
    rcases z with ⟨s, x⟩
    simp
  have hm := c13_time_translation_measurePreserving (d := d) t (t+a) (t+b) U
  have hm' : Measure.map (fun z : ℝ × Vec d => (z.1+t, z.2))
      (volume.restrict (Set.Ioo a b ×ˢ U)) =
      volume.restrict (Set.Ioo (t+a) (t+b) ×ˢ U) := by
    simpa only [add_sub_cancel_left] using hm.map_eq
  have hn := he.eLpNorm_map_measure (g := f) (p := p)
    (μ := volume.restrict (Set.Ioo a b ×ˢ U))
  rw [hm'] at hn
  simpa only [Function.comp_def, add_comm] using hn.symm

/-- The conditional unit gain transfers to a physical cylinder at any time
    origin, retaining the exact parabolic Jacobian. -/
theorem c9_time_shifted_signed_gain_with_jacobian
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (y : Vec d) (r : ℝ), 0 < r →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (t-r^2) (t+r^2)) (sourceBall y r) u G →
      ∀ p : ℝ, 2 ≤ p →
      let J : ℝ≥0∞ := ENNReal.ofReal |(r^2)⁻¹| *
        ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
      J ^ (1 / ENNReal.ofReal (p*((d:ℝ)+2)/d)).toReal *
        eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
          (volume.restrict (Set.Ioo (t-(r^2)/4) (t+r^2/4) ×ˢ sourceBall y (r/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        (J ^ (1 / ENNReal.ofReal p).toReal *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y r))) := by
  obtain ⟨C, hC, hgain⟩ := c9_centered_signed_gain_with_jacobian d κ hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro t y r hr ρ α hell u G hcal p hp
  have hc := c18_weighted_caloric_time_translate ρ α (-r^2) (r^2) t
    (sourceBall y r) u G (by simpa only [sub_eq_add_neg] using hcal)
  have h := hgain y r hr ρ α hell _ _ hc p hp
  simpa only [c9_time_shifted_cylinder_eLpNorm, sub_eq_add_neg, neg_div] using h

/-- The physical signed gain holds uniformly at all inner dyadic centres. -/
theorem c9_dyadic_local_signed_gain_with_jacobian
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ (n : ℕ) (t : ℝ) (y : Vec d),
      (t, y) ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)) →
      ∀ p : ℝ, 2 ≤ p →
      let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
      let J : ℝ≥0∞ := ENNReal.ofReal |(r^2)⁻¹| *
        ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
      J ^ (1 / ENNReal.ofReal (p*((d:ℝ)+2)/d)).toReal *
        eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
          (volume.restrict (Set.Ioo (t-(r^2)/4) (t+r^2/4) ×ˢ sourceBall y (r/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        (J ^ (1 / ENNReal.ofReal p).toReal *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y r))) := by
  obtain ⟨C, hC, hgain⟩ := c9_time_shifted_signed_gain_with_jacobian d κ hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal n t y hinner p hp
  exact hgain t y (1 / (8 * (2 : ℝ) ^ n))
    (c9_dyadic_parabolic_radius_bounds n).1 ρ α hell u G
    (c9_weighted_caloric_dyadic_local hcal n t y hinner) p hp

/-- The local signed gain is controlled by the norm on the preceding full
    dyadic cylinder. The unit gain is an explicit conditional input. -/
theorem c9_dyadic_local_signed_gain_global_rhs
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ (n : ℕ) (t : ℝ) (y : Vec d),
      (t, y) ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)) →
      ∀ p : ℝ, 2 ≤ p →
      let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
      let J : ℝ≥0∞ := ENNReal.ofReal |(r^2)⁻¹| *
        ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
      J ^ (1 / ENNReal.ofReal (p*((d:ℝ)+2)/d)).toReal *
        eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
          (volume.restrict (Set.Ioo (t-(r^2)/4) (t+r^2/4) ×ˢ sourceBall y (r/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        (J ^ (1 / ENNReal.ofReal p).toReal *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
              (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
              sourceBall 0 (1 / 2 + 1 / (2 * (2 : ℝ) ^ n))))) := by
  obtain ⟨C, hC, hlocal⟩ := c9_dyadic_local_signed_gain_with_jacobian d κ hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell u G hcal n t y hinner p hp
  have h := hlocal ρ α hell u G hcal n t y hinner p hp
  dsimp only at h ⊢
  have hmono := eLpNorm_mono_measure u (p := ENNReal.ofReal p)
    (Measure.restrict_mono_set volume (c9_dyadic_local_cylinder_containment d n t y hinner))
  exact h.trans (mul_le_mul (le_refl _)
    (mul_le_mul (le_refl _) hmono zero_le zero_le) zero_le zero_le)

/-- The transported signed gain applies to the actual Dirichlet kernel at
    every positive time centre, with its preceding dyadic-cylinder norm. -/
theorem c9_native_kernel_dyadic_local_signed_gain
    (d : ℕ) (κ : ℝ)
    (hSignedUnitGain :
      ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      ∀ p : ℝ, 2 ≤ p →
      eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
        (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsDirichletFundamentalSolution ρ α 1 K G →
      ∀ y₀ ∈ sourceBall (0 : Vec d) 1, ∀ t₀ : ℝ, 1 < t₀ →
      ∀ (n : ℕ) (t : ℝ) (y : Vec d),
      (t, y) ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall 0 (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)) →
      ∀ p : ℝ, 2 ≤ p →
      let r : ℝ := 1 / (8 * (2 : ℝ) ^ n)
      let J : ℝ≥0∞ := ENNReal.ofReal |(r^2)⁻¹| *
        ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)
      let u : ℝ × Vec d → ℝ := fun z => K (t₀ + z.1) z.2 y₀
      J ^ (1 / ENNReal.ofReal (p*((d:ℝ)+2)/d)).toReal *
        eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
          (volume.restrict (Set.Ioo (t-(r^2)/4) (t+r^2/4) ×ˢ sourceBall y (r/2))) ≤
      ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        (J ^ (1 / ENNReal.ofReal p).toReal *
          eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (-(1 / 4) - 3 / (4 * (2 : ℝ) ^ n))
              (1 / 4 + 3 / (4 * (2 : ℝ) ^ n)) ×ˢ
              sourceBall 0 (1 / 2 + 1 / (2 * (2 : ℝ) ^ n))))) := by
  obtain ⟨C, hC, hlocal⟩ := c9_dyadic_local_signed_gain_global_rhs d κ hSignedUnitGain
  refine ⟨C, hC, ?_⟩
  intro ρ α hell K G hK y₀ hy₀ t₀ ht₀ n t y hinner p hp
  have ha : 0 < t₀ + (-1 : ℝ) := by linarith
  have hab : t₀ + (-1 : ℝ) < t₀ + 1 := by linarith
  have hcal := ((hK y₀ hy₀).2.2.2.1 (t₀ + (-1)) (t₀ + 1) ha hab).1
  have hc := c18_weighted_caloric_time_translate ρ α (-1) 1 t₀
    (sourceBall 0 1) (fun z => K z.1 z.2 y₀) (fun z => G z.1 z.2 y₀) hcal
  exact hlocal ρ α hell _ _ hc n t y hinner p hp

/-- Iterating a fixed half-radius net yields geometric covering cardinality. -/
theorem c9_iterated_half_radius_net {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset E)
    (hS : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ S, ‖x - y‖ ≤ 1 / 2) :
    ∀ n : ℕ, ∃ T : Finset E, T.card ≤ S.card ^ n ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ T, ‖x - y‖ ≤ (1 / 2 : ℝ) ^ n := by
  classical
  intro n
  induction n with
  | zero =>
    refine ⟨{0}, by simp, ?_⟩
    intro x hx
    exact ⟨0, by simp, by simpa using hx⟩
  | succ n ih =>
    obtain ⟨T, hcard, hcover⟩ := ih
    let r : ℝ := (1 / 2 : ℝ) ^ n
    have hr : 0 < r := by dsimp [r]; positivity
    let U : Finset E := (T.product S).image (fun z => z.1 + r • z.2)
    refine ⟨U, ?_, ?_⟩
    · calc
        U.card ≤ (T.product S).card := Finset.card_image_le
        _ = T.card * S.card := Finset.card_product _ _
        _ ≤ S.card ^ n * S.card := Nat.mul_le_mul_right _ hcard
        _ = S.card ^ (n + 1) := by rw [pow_succ]
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := hcover x hx
      change ‖x - a‖ ≤ r at hxa
      have hy : ‖r⁻¹ • (x - a)‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        rw [← div_eq_inv_mul]
        exact (div_le_one hr).2 hxa
      obtain ⟨b, hb, hxb⟩ := hS (r⁻¹ • (x - a)) hy
      refine ⟨a + r • b, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
      · have heq : x - (a + r • b) = r • (r⁻¹ • (x - a) - b) := by
          rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
          abel
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr, pow_succ]
        exact mul_le_mul_of_nonneg_left hxb hr.le

/-- A finite half-radius net of the unit ball exists in finite dimension. -/
theorem c9_finite_half_radius_net {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ S : Finset E, ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ S, ‖x - y‖ ≤ 1 / 2 := by
  classical
  have hk : IsCompact (Metric.closedBall (0 : E) 1) := isCompact_closedBall 0 1
  obtain ⟨s, hs, hfin, hcover⟩ := hk.finite_cover_balls (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨hfin.toFinset, ?_⟩
  intro x hx
  have hxb : x ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hxc := hcover hxb
  simp only [Set.mem_iUnion] at hxc
  obtain ⟨y, hy, hxy⟩ := hxc
  refine ⟨y, hfin.mem_toFinset.mpr hy, ?_⟩
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hxy)

/-- The unit ball admits dyadic nets with a geometric cardinality bound. -/
theorem c9_geometric_unit_ball_nets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ M : ℕ, ∀ n : ℕ, ∃ T : Finset E, T.card ≤ M ^ n ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ T, ‖x - y‖ ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨S, hS⟩ := c9_finite_half_radius_net (E := E)
  exact ⟨S.card, c9_iterated_half_radius_net S hS⟩

/-- A finite net can be recentered in its covered set at twice the radius. -/
theorem c9_recenter_net {E : Type*} [PseudoMetricSpace E] (A : Set E) (ε : ℝ)
    (T : Finset E) (hT : ∀ x ∈ A, ∃ y ∈ T, dist x y ≤ ε) :
    ∃ U : Finset E, U.card ≤ T.card ∧ (∀ y ∈ U, y ∈ A) ∧
      ∀ x ∈ A, ∃ y ∈ U, dist x y ≤ 2 * ε := by
  classical
  let P : E → Prop := fun y => ∃ x ∈ A, dist x y ≤ ε
  let T' := T.filter P
  let f : E → E := fun y => if h : P y then Classical.choose h else y
  have hf (y : E) (hy : y ∈ T') : f y ∈ A ∧ dist (f y) y ≤ ε := by
    have hp : P y := (Finset.mem_filter.mp hy).2
    simpa only [f, dite_eq_left hp] using Classical.choose_spec hp
  let U := T'.image f
  refine ⟨U, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact (hf z hz).1
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := hT x hx
    have hz' : z ∈ T' := Finset.mem_filter.mpr ⟨hz, ⟨x, hx, hxz⟩⟩
    refine ⟨f z, Finset.mem_image.mpr ⟨z, hz', rfl⟩, ?_⟩
    have hd := dist_triangle x z (f z)
    have hfz := (hf z hz').2
    rw [dist_comm z (f z)] at hd
    linarith

/-- Every subset of the unit ball has internal dyadic nets of geometric size. -/
theorem c9_geometric_internal_nets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : Set E)
    (hA : ∀ x ∈ A, ‖x‖ ≤ 1) :
    ∃ M : ℕ, ∀ n : ℕ, ∃ U : Finset E, U.card ≤ M ^ n ∧
      (∀ y ∈ U, y ∈ A) ∧
      ∀ x ∈ A, ∃ y ∈ U, dist x y ≤ 2 * (1 / 2 : ℝ) ^ n := by
  obtain ⟨M, hnet⟩ := c9_geometric_unit_ball_nets (E := E)
  refine ⟨M, ?_⟩
  intro n
  obtain ⟨T, hcard, hcover⟩ := hnet n
  have hT : ∀ x ∈ A, ∃ y ∈ T, dist x y ≤ (1 / 2 : ℝ) ^ n := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x (hA x hx)
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy⟩
  obtain ⟨U, hU, hUA, hcoverU⟩ := c9_recenter_net A _ T hT
  exact ⟨U, hU.trans hcard, hUA, hcoverU⟩

/-- Internal nets at a prescribed quadratic dyadic scale have geometric size. -/
theorem c9_quadratic_dyadic_internal_nets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : Set E)
    (hA : ∀ x ∈ A, ‖x‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C B : ℕ, ∀ n : ℕ, ∃ U : Finset E, U.card ≤ C * B ^ n ∧
      (∀ y ∈ U, y ∈ A) ∧
      ∀ x ∈ A, ∃ y ∈ U, dist x y < δ * (1 / 4 : ℝ) ^ n := by
  obtain ⟨M, hnet⟩ := c9_geometric_internal_nets A hA
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨M ^ k, M ^ 2, ?_⟩
  intro n
  obtain ⟨U, hcard, hcenter, hcover⟩ := hnet (k + 2 * n)
  refine ⟨U, ?_, hcenter, ?_⟩
  · simpa only [pow_add, pow_mul] using hcard
  · intro x hx
    obtain ⟨y, hy, hdist⟩ := hcover x hx
    refine ⟨y, hy, hdist.trans_lt ?_⟩
    have hp : (1 / 2 : ℝ) ^ (k + 2 * n) =
        (1 / 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ n := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hp]
    have hpn : 0 < (1 / 4 : ℝ) ^ n := by positivity
    nlinarith

/-- The same geometric cardinality bound works for all subsets of the unit ball. -/
theorem c9_uniform_quadratic_internal_nets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (δ : ℝ) (hδ : 0 < δ) :
    ∃ C B : ℕ, ∀ n : ℕ, ∀ A : Set E, (∀ x ∈ A, ‖x‖ ≤ 1) →
      ∃ U : Finset E, U.card ≤ C * B ^ n ∧ (∀ y ∈ U, y ∈ A) ∧
        ∀ x ∈ A, ∃ y ∈ U, dist x y < δ * (1 / 4 : ℝ) ^ n := by
  let D : Set E := Metric.closedBall 0 1
  have hD : ∀ x ∈ D, ‖x‖ ≤ 1 := by
    intro x hx
    simpa only [D, Metric.mem_closedBall, dist_zero_right] using hx
  obtain ⟨C, B, hnet⟩ := c9_quadratic_dyadic_internal_nets D hD (δ / 4)
    (by positivity)
  refine ⟨C, B, ?_⟩
  intro n A hA
  obtain ⟨T, hcard, _, hcover⟩ := hnet n
  have hT : ∀ x ∈ A, ∃ y ∈ T, dist x y ≤
      (δ / 4) * (1 / 4 : ℝ) ^ n := by
    intro x hx
    have hxD : x ∈ D := by
      simpa only [D, Metric.mem_closedBall, dist_zero_right] using hA x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hxD
    exact ⟨y, hy, le_of_lt hxy⟩
  obtain ⟨U, hUT, hUA, hUC⟩ := c9_recenter_net A _ T hT
  refine ⟨U, hUT.trans hcard, hUA, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hUC x hx
  /- Recenter at a smaller tolerance to keep the final bound strict. -/
  refine ⟨y, hy, ?_⟩
  have hpos : 0 < δ * (1 / 4 : ℝ) ^ n := by positivity
  nlinarith

/-- Each inner dyadic cylinder lies in the unit ball of the product norm. -/
theorem c9_dyadic_inner_cylinder_subset_unit_ball (d n : ℕ) :
    ∀ z ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
      (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
      sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)),
      ‖z‖ ≤ 1 := by
  intro z hz
  rcases hz with ⟨⟨ht₁, ht₂⟩, hy⟩
  have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have htime : 3 / (8 * (2 : ℝ) ^ n) ≤ 3 / 8 := by
    rw [div_le_iff₀ (by positivity : 0 < 8 * (2 : ℝ) ^ n)]
    nlinarith
  have hspace : 1 / (4 * (2 : ℝ) ^ n) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * (2 : ℝ) ^ n)]
    nlinarith
  change euclideanNorm (z.2 - 0) < _ at hy
  simp only [sub_zero] at hy
  rw [norm_prod_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  · have hs := c18_norm_le_euclideanNorm z.2
    linarith

/-- Uniformly many product-metric balls cover each inner dyadic cylinder. -/
theorem c9_dyadic_inner_cylinder_quadratic_nets (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C B : ℕ, ∀ n : ℕ, ∃ U : Finset (ℝ × Vec d), U.card ≤ C * B ^ n ∧
      (∀ y ∈ U, y ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n))) ∧
      ∀ x ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)),
        ∃ y ∈ U, dist x y < δ * (1 / 4 : ℝ) ^ n := by
  obtain ⟨C, B, hnet⟩ := c9_uniform_quadratic_internal_nets
    (E := ℝ × Vec d) δ hδ
  refine ⟨C, B, ?_⟩
  intro n
  exact hnet n _ (c9_dyadic_inner_cylinder_subset_unit_ball d n)

/-- A product-metric ball at parabolic scale fits the inner cylinder used by
    the transported signed gain. -/
theorem c9_product_metric_ball_in_inner_parabolic_cylinder (d : ℕ)
    (x y : ℝ × Vec d) (r ε : ℝ)
    (htime : ε ≤ r ^ 2 / 4) (hspace : ((d : ℝ) + 1) * ε ≤ r / 2)
    (hxy : dist x y < ε) :
    x ∈ Set.Ioo (y.1 - r ^ 2 / 4) (y.1 + r ^ 2 / 4) ×ˢ
      sourceBall y.2 (r / 2) := by
  have hd : ‖x - y‖ < ε := by simpa only [dist_eq_norm] using hxy
  have ht : |x.1 - y.1| < ε := by
    have h := (norm_fst_le (x - y)).trans_lt hd
    simpa only [Prod.fst_sub, Real.norm_eq_abs] using h
  have hs : ‖x.2 - y.2‖ < ε := by
    have h := (norm_snd_le (x - y)).trans_lt hd
    simpa only [Prod.snd_sub] using h
  have hdim : 0 < (d : ℝ) + 1 := by positivity
  have he := (euclideanNorm_le_dimension_mul_norm (x.2 - y.2)).trans_lt
    (mul_lt_mul_of_pos_left hs hdim)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := (abs_lt.mp ht).1
    linarith
  · have := (abs_lt.mp ht).2
    linarith
  · change euclideanNorm (x.2 - y.2) < r / 2
    exact he.trans_le hspace

/-- A quadratic-scale net gives a geometric parabolic covering, once its
    scale satisfies the explicit time and space radius inequalities. -/
theorem c9_dyadic_inner_cylinder_parabolic_cover_of_scale (d : ℕ) (δ : ℝ)
    (hδ : 0 < δ)
    (htime : ∀ n : ℕ, δ * (1 / 4 : ℝ) ^ n ≤
      (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4)
    (hspace : ∀ n : ℕ, ((d : ℝ) + 1) * (δ * (1 / 4 : ℝ) ^ n) ≤
      (1 / (8 * (2 : ℝ) ^ n)) / 2) :
    ∃ C B : ℕ, ∀ n : ℕ, ∃ U : Finset (ℝ × Vec d), U.card ≤ C * B ^ n ∧
      (∀ y ∈ U, y ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n))) ∧
      ∀ x ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)),
        ∃ y ∈ U, x ∈
          Set.Ioo (y.1 - (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4)
            (y.1 + (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4) ×ˢ
          sourceBall y.2 ((1 / (8 * (2 : ℝ) ^ n)) / 2) := by
  obtain ⟨C, B, hnet⟩ := c9_dyadic_inner_cylinder_quadratic_nets d δ hδ
  refine ⟨C, B, ?_⟩
  intro n
  obtain ⟨U, hcard, hcenters, hcover⟩ := hnet n
  refine ⟨U, hcard, hcenters, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hcover x hx
  exact ⟨y, hy, c9_product_metric_ball_in_inner_parabolic_cylinder d x y
    _ _ (htime n) (hspace n) hxy⟩

/-- A dimension-dependent fixed scale fits both parabolic radii at every
    dyadic level. -/
theorem c9_dyadic_parabolic_cover_scale (d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ n : ℕ, δ * (1 / 4 : ℝ) ^ n ≤
        (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4) ∧
      (∀ n : ℕ, ((d : ℝ) + 1) * (δ * (1 / 4 : ℝ) ^ n) ≤
        (1 / (8 * (2 : ℝ) ^ n)) / 2) := by
  let D : ℝ := (d : ℝ) + 1
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hDp : 0 < D := by linarith
  let δ : ℝ := 1 / (512 * D)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbound : δ ≤ 1 / 256 := by
    dsimp [δ]
    rw [div_le_iff₀ (by positivity : 0 < 512 * D)]
    nlinarith
  have hDδ : D * δ = 1 / 512 := by
    dsimp [δ]
    field_simp
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro n
    have hz : 0 < (2 : ℝ) ^ n := by positivity
    have hfour : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    have hq : (1 / 4 : ℝ) ^ n = 1 / ((2 : ℝ) ^ n) ^ 2 := by
      simp only [one_div, inv_pow]
      rw [hfour]
    rw [hq]
    have heq : (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4 =
        (1 / 256 : ℝ) * (1 / ((2 : ℝ) ^ n) ^ 2) := by
      field_simp
      <;> ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hδbound (by positivity)
  · intro n
    have hz : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hzp : 0 < (2 : ℝ) ^ n := by positivity
    have hfour : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    have hq : (1 / 4 : ℝ) ^ n = 1 / ((2 : ℝ) ^ n) ^ 2 := by
      simp only [one_div, inv_pow]
      rw [hfour]
    change D * (δ * (1 / 4 : ℝ) ^ n) ≤ _
    rw [← mul_assoc, hDδ, hq]
    have hqle : 1 / ((2 : ℝ) ^ n) ^ 2 ≤ 1 / (2 : ℝ) ^ n := by
      rw [div_le_div_iff₀ (by positivity : 0 < ((2 : ℝ) ^ n) ^ 2) hzp]
      nlinarith
    have hbound := mul_le_mul_of_nonneg_left hqle (show (0 : ℝ) ≤ 1 / 512 by norm_num)
    have heq : (1 / (8 * (2 : ℝ) ^ n)) / 2 =
        (1 / 16 : ℝ) * (1 / (2 : ℝ) ^ n) := by field_simp <;> norm_num
    rw [heq]
    nlinarith [div_pos (show (0 : ℝ) < 1 by norm_num) hzp]

/-- The actual inner dyadic cylinders admit geometric finite parabolic covers. -/
theorem c9_dyadic_inner_cylinder_parabolic_cover (d : ℕ) :
    ∃ C B : ℕ, ∀ n : ℕ, ∃ U : Finset (ℝ × Vec d), U.card ≤ C * B ^ n ∧
      (∀ y ∈ U, y ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n))) ∧
      ∀ x ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)),
        ∃ y ∈ U, x ∈
          Set.Ioo (y.1 - (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4)
            (y.1 + (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4) ×ˢ
          sourceBall y.2 ((1 / (8 * (2 : ℝ) ^ n)) / 2) := by
  obtain ⟨δ, hδ, htime, hspace⟩ := c9_dyadic_parabolic_cover_scale d
  exact c9_dyadic_inner_cylinder_parabolic_cover_of_scale d δ hδ htime hspace

/-- A finite cover bounds the integral by the sum of its local integrals,
    without requiring disjointness or measurability of the covering sets. -/
theorem c9_lintegral_le_finset_cover {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (A : Set X) (U : Finset I)
    (V : I → Set X) (hcover : A ⊆ ⋃ i ∈ U, V i) :
    (∫⁻ x in A, f x ∂μ) ≤ ∑ i ∈ U, ∫⁻ x in V i, f x ∂μ := by
  classical
  have hsum : (∫⁻ x in ⋃ i ∈ U, V i, f x ∂μ) ≤
      ∑ i ∈ U, ∫⁻ x in V i, f x ∂μ := by
    clear hcover
    induction U using Finset.induction_on with
    | empty => simp
    | @insert i U hi ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
      exact (lintegral_union_le f _ _).trans (add_le_add_right ih _)
  exact (lintegral_mono' (Measure.restrict_mono_set μ hcover) le_rfl).trans hsum

/-- Integrating over the inner cylinder is bounded by the sum of its
    geometrically many local parabolic-cylinder integrals. -/
theorem c9_dyadic_inner_lintegral_parabolic_cover (d : ℕ) :
    ∃ C B : ℕ, ∀ n : ℕ, ∃ U : Finset (ℝ × Vec d), U.card ≤ C * B ^ n ∧
      (∀ y ∈ U, y ∈ Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
        (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
        sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n))) ∧
      ∀ f : (ℝ × Vec d) → ℝ≥0∞,
        (∫⁻ x in Set.Ioo (-(1 / 4) - 3 / (8 * (2 : ℝ) ^ n))
          (1 / 4 + 3 / (8 * (2 : ℝ) ^ n)) ×ˢ
          sourceBall (0 : Vec d) (1 / 2 + 1 / (4 * (2 : ℝ) ^ n)), f x ∂volume) ≤
        ∑ y ∈ U, ∫⁻ x in
          Set.Ioo (y.1 - (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4)
            (y.1 + (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4) ×ˢ
          sourceBall y.2 ((1 / (8 * (2 : ℝ) ^ n)) / 2), f x ∂volume := by
  obtain ⟨C, B, hcover⟩ := c9_dyadic_inner_cylinder_parabolic_cover d
  refine ⟨C, B, ?_⟩
  intro n
  obtain ⟨U, hcard, hcenter, hU⟩ := hcover n
  refine ⟨U, hcard, hcenter, ?_⟩
  intro f
  apply c9_lintegral_le_finset_cover volume f _ U
    (fun y => Set.Ioo (y.1 - (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4)
      (y.1 + (1 / (8 * (2 : ℝ) ^ n)) ^ 2 / 4) ×ˢ
      sourceBall y.2 ((1 / (8 * (2 : ℝ) ^ n)) / 2))
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hU x hx
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hxy⟩⟩

open Classical in
/-- Within one time slab, spatially separated centers have uniformly bounded
multiplicity on the outer parabolic cylinders. -/
theorem c9_parabolic_slab_spatial_overlap (d : ℕ) (U : Finset (Vec d))
    (t r : ℝ) (hr : 0 < r)
    (hsep : ∀ y ∈ U, ∀ z ∈ U, y ≠ z → r ≤ ‖y-z‖)
    (x : ℝ × Vec d) :
    (U.filter (fun y => x ∈ Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r))).card
      ≤ 5 ^ Module.finrank ℝ (Vec d) := by
  classical
  apply c17_card_separated_near_point _ x.2 r hr
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2.2
    change euclideanNorm (x.2-y) < 2*r at hy'
    have hn := (c18_norm_le_euclideanNorm (x.2-y)).trans (le_of_lt hy')
    simpa only [norm_sub_rev] using hn
  · intro y hy z hz hyz
    exact hsep y (Finset.mem_filter.mp hy).1 z (Finset.mem_filter.mp hz).1 hyz

open Classical in
/-- Summing separated spatial families over finitely many time slabs bounds
outer-cylinder multiplicity by the number of slabs times the packing bound. -/
theorem c9_parabolic_time_slab_overlap (d : ℕ) (T : Finset ℝ)
    (U : ℝ → Finset (Vec d)) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ t ∈ T, ∀ y ∈ U t, ∀ z ∈ U t, y ≠ z → r ≤ ‖y-z‖)
    (x : ℝ × Vec d) :
    (∑ t ∈ T, ((U t).filter
      (fun y => x ∈ Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r))).card)
      ≤ T.card * 5 ^ Module.finrank ℝ (Vec d) := by
  classical
  calc
    _ ≤ ∑ _t ∈ T, 5 ^ Module.finrank ℝ (Vec d) := by
      apply Finset.sum_le_sum
      intro t ht
      exact c9_parabolic_slab_spatial_overlap d (U t) t r hr (hsep t ht) x
    _ = _ := by simp

open Classical in
/-- Only time slabs containing the point can contribute to the outer-cylinder
multiplicity. -/
theorem c9_parabolic_active_slab_overlap (d : ℕ) (T : Finset ℝ)
    (U : ℝ → Finset (Vec d)) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ t ∈ T, ∀ y ∈ U t, ∀ z ∈ U t, y ≠ z → r ≤ ‖y-z‖)
    (x : ℝ × Vec d) :
    (∑ t ∈ T, ((U t).filter
      (fun y => x ∈ Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r))).card)
      ≤ (T.filter (fun t => x.1 ∈ Set.Ioo (t-r^2) (t+r^2))).card *
        5 ^ Module.finrank ℝ (Vec d) := by
  classical
  let T' := T.filter (fun t => x.1 ∈ Set.Ioo (t-r^2) (t+r^2))
  have hsum : (∑ t ∈ T, ((U t).filter
      (fun y => x ∈ Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r))).card) =
      ∑ t ∈ T', ((U t).filter
        (fun y => x ∈ Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r))).card := by
    dsimp only [T']
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hx : x.1 ∈ Set.Ioo (t-r^2) (t+r^2)
    · simp [hx]
    · simp [hx, Set.mem_prod]
  rw [hsum]
  exact c9_parabolic_time_slab_overlap d T' U r hr
    (fun t ht => hsep t (Finset.mem_filter.mp ht).1) x

open Classical in
/-- Parabolically separated time centers and separated spatial centers give a
uniform overlap bound for the outer cylinders. -/
theorem c9_parabolic_separated_slab_overlap (d : ℕ) (T : Finset ℝ)
    (U : ℝ → Finset (Vec d)) (r : ℝ) (hr : 0 < r)
    (htsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → r^2 ≤ |t-s|)
    (hsep : ∀ t ∈ T, ∀ y ∈ U t, ∀ z ∈ U t, y ≠ z → r ≤ ‖y-z‖)
    (x : ℝ × Vec d) :
    (∑ t ∈ T, ((U t).filter
      (fun y => x ∈ Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r))).card)
      ≤ 5 * 5 ^ Module.finrank ℝ (Vec d) := by
  classical
  have hnear : ∀ t ∈ T.filter (fun t => x.1 ∈ Set.Ioo (t-r^2) (t+r^2)),
      ‖t-x.1‖ ≤ 2 * r^2 := by
    intro t ht
    have hmem := (Finset.mem_filter.mp ht).2
    rw [Real.norm_eq_abs, abs_le]
    have hs : 0 ≤ r^2 := sq_nonneg r
    constructor <;> linarith [hmem.1, hmem.2]
  have htsep' : ∀ t ∈ T.filter (fun t => x.1 ∈ Set.Ioo (t-r^2) (t+r^2)),
      ∀ s ∈ T.filter (fun t => x.1 ∈ Set.Ioo (t-r^2) (t+r^2)),
      t ≠ s → r^2 ≤ ‖t-s‖ := by
    intro t ht s hs hne
    simpa only [Real.norm_eq_abs] using
      htsep t (Finset.mem_filter.mp ht).1 s (Finset.mem_filter.mp hs).1 hne
  have htime : (T.filter (fun t => x.1 ∈ Set.Ioo (t-r^2) (t+r^2))).card ≤ 5 := by
    simpa using c17_card_separated_near_point _ x.1 (r^2) (sq_pos_of_pos hr) hnear htsep'
  exact (c9_parabolic_active_slab_overlap d T U r hr hsep x).trans
    (Nat.mul_le_mul_right _ htime)

/-- Separated parabolic slabs control the sum of their outer moments. -/
theorem c9_parabolic_separated_slab_lintegral (d : ℕ) (T : Finset ℝ)
    (U : ℝ → Finset (Vec d)) (r : ℝ) (hr : 0 < r)
    (htsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → r^2 ≤ |t-s|)
    (hsep : ∀ t ∈ T, ∀ y ∈ U t, ∀ z ∈ U t, y ≠ z → r ≤ ‖y-z‖)
    (A : Set (ℝ × Vec d)) (hA : MeasurableSet A)
    (hcontain : ∀ t ∈ T, ∀ y ∈ U t,
      Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r) ⊆ A)
    (f : (ℝ × Vec d) → ℝ≥0∞) (hf : AEMeasurable f volume) :
    (∑ t ∈ T, ∑ y ∈ U t, ∫⁻ x in
      Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r), f x ∂volume) ≤
      (↑(5 * 5 ^ Module.finrank ℝ (Vec d)) : ℝ≥0∞) * ∫⁻ x in A, f x ∂volume := by
  classical
  let V : (Σ _t : ℝ, Vec d) → Set (ℝ × Vec d) := fun p =>
    Set.Ioo (p.1-r^2) (p.1+r^2) ×ˢ sourceBall p.2 (2*r)
  have hV : ∀ p ∈ T.sigma U, MeasurableSet (V p) := by
    intro p hp
    exact measurableSet_Ioo.prod (c17_isOpen_sourceBall _ _).measurableSet
  have hoverlap : ∀ x, (∑ p ∈ T.sigma U,
      (V p).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
      (↑(5 * 5 ^ Module.finrank ℝ (Vec d)) : ℝ≥0∞) *
        A.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    have hcount := c9_parabolic_separated_slab_overlap d T U r hr htsep hsep x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, mul_one]
      rw [Finset.sum_sigma]
      have heq : (∑ t ∈ T, ∑ y ∈ U t,
          (V ⟨t, y⟩).indicator (fun _ => (1 : ℝ≥0∞)) x) =
          (↑(∑ t ∈ T, ((U t).filter (fun y => x ∈ V ⟨t, y⟩)).card) : ℝ≥0∞) := by
        simp only [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro t ht
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        simp
      rw [heq]
      exact_mod_cast hcount
    · simp only [Set.indicator_of_notMem hx, mul_zero, nonpos_iff_eq_zero]
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := Finset.mem_sigma.mp hp
      have hn : x ∉ V p := fun h => hx (hcontain p.1 hp'.1 p.2 hp'.2 h)
      simp [hn]
  have h := c17_lintegral_sum_le_of_bounded_overlap volume (T.sigma U) V A hV hA
    (↑(5 * 5 ^ Module.finrank ℝ (Vec d))) f hf hoverlap
  simpa only [Finset.sum_sigma, V] using h

open Classical in
/-- A bounded-overlap parabolic cover transports local moment estimates. -/
theorem c9_bounded_overlap_moment_transport (d : ℕ) (F : Finset (ℝ × Vec d))
    (r : ℝ) (A D : Set (ℝ × Vec d)) (N : ℕ) (hA : MeasurableSet A)
    (hcontain : ∀ z ∈ F, Set.Ioo (z.1-r^2) (z.1+r^2) ×ˢ sourceBall z.2 (2*r) ⊆ A)
    (hcover : ∀ x ∈ D, ∃ z ∈ F, x ∈ Set.Ioo (z.1-r^2/4) (z.1+r^2/4) ×ˢ sourceBall z.2 (r/2))
    (hoverlap : ∀ x : ℝ × Vec d, (F.filter (fun z => x ∈ Set.Ioo (z.1-r^2) (z.1+r^2) ×ˢ sourceBall z.2 (2*r))).card ≤ N)
    (f g : (ℝ × Vec d) → ℝ≥0∞) (hf : AEMeasurable f volume)
    (s : ℝ) (hs : 0 ≤ s) (L : ℝ≥0∞)
    (hlocal : ∀ z ∈ F,
      (∫⁻ x in Set.Ioo (z.1-r^2/4) (z.1+r^2/4) ×ˢ sourceBall z.2 (r/2), g x ∂volume) ≤
        L * (∫⁻ x in Set.Ioo (z.1-r^2) (z.1+r^2) ×ˢ sourceBall z.2 (2*r), f x ∂volume) ^ s *
          (∫⁻ x in Set.Ioo (z.1-r^2) (z.1+r^2) ×ˢ sourceBall z.2 (2*r), f x ∂volume)) :
    (∫⁻ x in D, g x ∂volume) ≤
      L * (∫⁻ x in A, f x ∂volume) ^ s * ((N : ℝ≥0∞) * ∫⁻ x in A, f x ∂volume) := by
  classical
  let V : (ℝ × Vec d) → Set (ℝ × Vec d) := fun z =>
    Set.Ioo (z.1-r^2/4) (z.1+r^2/4) ×ˢ sourceBall z.2 (r/2)
  let W : (ℝ × Vec d) → Set (ℝ × Vec d) := fun z =>
    Set.Ioo (z.1-r^2) (z.1+r^2) ×ˢ sourceBall z.2 (2*r)
  have hcov : D ⊆ ⋃ z ∈ F, V z := by
    intro x hx
    obtain ⟨z, hz, hxyz⟩ := hcover x hx
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hxyz⟩⟩
  have hW : ∀ z ∈ F, MeasurableSet (W z) := by
    intro z hz
    exact measurableSet_Ioo.prod (c17_isOpen_sourceBall _ _).measurableSet
  have hcount : ∀ x, (∑ z ∈ F, (W z).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
      (N : ℝ≥0∞) * A.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, mul_one]
      have heq : (∑ z ∈ F, (W z).indicator (fun _ => (1 : ℝ≥0∞)) x) =
          ((F.filter (fun z => x ∈ W z)).card : ℝ≥0∞) := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        simp
      rw [heq]
      exact_mod_cast hoverlap x
    · simp only [Set.indicator_of_notMem hx, mul_zero, nonpos_iff_eq_zero]
      apply Finset.sum_eq_zero
      intro z hz
      have hn : x ∉ W z := fun h => hx (hcontain z hz h)
      simp [hn]
  have houter := c17_lintegral_sum_le_of_bounded_overlap volume F W A hW hA
    (N : ℝ≥0∞) f hf hcount
  calc
    (∫⁻ x in D, g x ∂volume) ≤ ∑ z ∈ F, ∫⁻ x in V z, g x ∂volume :=
      c9_lintegral_le_finset_cover volume g D F V hcov
    _ ≤ ∑ z ∈ F, L * (∫⁻ x in A, f x ∂volume) ^ s *
        (∫⁻ x in W z, f x ∂volume) := by
      apply Finset.sum_le_sum
      intro z hz
      have hmono : (∫⁻ x in W z, f x ∂volume) ≤ ∫⁻ x in A, f x ∂volume :=
        lintegral_mono' (Measure.restrict_mono_set volume (hcontain z hz)) le_rfl
      exact (hlocal z hz).trans (by gcongr)
    _ = L * (∫⁻ x in A, f x ∂volume) ^ s *
        (∑ z ∈ F, ∫⁻ x in W z, f x ∂volume) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right houter _

/-- A separated parabolic cover combines local moment gains without a
cardinality loss: only the uniform outer-cylinder overlap remains. -/
theorem c9_parabolic_separated_slab_moment_transport (d : ℕ) (T : Finset ℝ)
    (U : ℝ → Finset (Vec d)) (r : ℝ) (hr : 0 < r)
    (htsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → r^2 ≤ |t-s|)
    (hsep : ∀ t ∈ T, ∀ y ∈ U t, ∀ z ∈ U t, y ≠ z → r ≤ ‖y-z‖)
    (A D : Set (ℝ × Vec d)) (hA : MeasurableSet A)
    (hcontain : ∀ t ∈ T, ∀ y ∈ U t,
      Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r) ⊆ A)
    (hcover : ∀ x ∈ D, ∃ t ∈ T, ∃ y ∈ U t,
      x ∈ Set.Ioo (t-r^2/4) (t+r^2/4) ×ˢ sourceBall y (r/2))
    (f g : (ℝ × Vec d) → ℝ≥0∞) (hf : AEMeasurable f volume)
    (s : ℝ) (hs : 0 ≤ s) (L : ℝ≥0∞)
    (hlocal : ∀ t ∈ T, ∀ y ∈ U t,
      (∫⁻ x in Set.Ioo (t-r^2/4) (t+r^2/4) ×ˢ sourceBall y (r/2), g x ∂volume) ≤
        L * (∫⁻ x in Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r), f x ∂volume) ^ s *
          (∫⁻ x in Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r), f x ∂volume)) :
    (∫⁻ x in D, g x ∂volume) ≤
      L * (∫⁻ x in A, f x ∂volume) ^ s *
        ((↑(5 * 5 ^ Module.finrank ℝ (Vec d)) : ℝ≥0∞) * ∫⁻ x in A, f x ∂volume) := by
  classical
  let V : (Σ _t : ℝ, Vec d) → Set (ℝ × Vec d) := fun p =>
    Set.Ioo (p.1-r^2/4) (p.1+r^2/4) ×ˢ sourceBall p.2 (r/2)
  let W : (Σ _t : ℝ, Vec d) → Set (ℝ × Vec d) := fun p =>
    Set.Ioo (p.1-r^2) (p.1+r^2) ×ˢ sourceBall p.2 (2*r)
  have hcov : D ⊆ ⋃ p ∈ T.sigma U, V p := by
    intro x hx
    obtain ⟨t, ht, y, hy, hxy⟩ := hcover x hx
    exact Set.mem_iUnion.mpr ⟨⟨t, y⟩, Set.mem_iUnion.mpr ⟨Finset.mem_sigma.mpr ⟨ht, hy⟩, hxy⟩⟩
  have houter := c9_parabolic_separated_slab_lintegral d T U r hr htsep hsep A hA hcontain f hf
  calc
    (∫⁻ x in D, g x ∂volume) ≤ ∑ p ∈ T.sigma U, ∫⁻ x in V p, g x ∂volume :=
      c9_lintegral_le_finset_cover volume g D (T.sigma U) V hcov
    _ ≤ ∑ p ∈ T.sigma U, L * (∫⁻ x in A, f x ∂volume) ^ s *
        (∫⁻ x in W p, f x ∂volume) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨ht, hy⟩ := Finset.mem_sigma.mp hp
      have hmono : (∫⁻ x in W p, f x ∂volume) ≤ ∫⁻ x in A, f x ∂volume :=
        lintegral_mono' (Measure.restrict_mono_set volume (hcontain p.1 ht p.2 hy)) le_rfl
      exact (hlocal p.1 ht p.2 hy).trans (by gcongr)
    _ = L * (∫⁻ x in A, f x ∂volume) ^ s *
        (∑ p ∈ T.sigma U, ∫⁻ x in W p, f x ∂volume) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      exact mul_le_mul_right (by simpa only [Finset.sum_sigma, W] using houter) _

/-- A local norm gain on separated slabs gives a global signed moment gain. -/
theorem c9_parabolic_separated_slab_norm_moment_transport
    (d : ℕ) (T : Finset ℝ) (U : ℝ → Finset (Vec d)) (r : ℝ) (hr : 0 < r)
    (htsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → r^2 ≤ |t-s|)
    (hsep : ∀ t ∈ T, ∀ y ∈ U t, ∀ z ∈ U t, y ≠ z → r ≤ ‖y-z‖)
    (A D : Set (ℝ × Vec d)) (hA : MeasurableSet A)
    (hcontain : ∀ t ∈ T, ∀ y ∈ U t,
      Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r) ⊆ A)
    (hcover : ∀ x ∈ D, ∃ t ∈ T, ∃ y ∈ U t,
      x ∈ Set.Ioo (t-r^2/4) (t+r^2/4) ×ˢ sourceBall y (r/2))
    (u : ℝ × Vec d → ℝ) (hu : AEStronglyMeasurable u volume)
    (p s : ℝ) (hp : 0 < p) (hs : 0 ≤ s) (L : ℝ≥0∞)
    (hlocal : ∀ t ∈ T, ∀ y ∈ U t,
      eLpNorm u (ENNReal.ofReal (p * (1+s)))
        (volume.restrict (Set.Ioo (t-r^2/4) (t+r^2/4) ×ˢ sourceBall y (r/2))) ≤
      L * eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (t-r^2) (t+r^2) ×ˢ sourceBall y (2*r)))) :
    (∫⁻ x in D, ‖u x‖ₑ ^ (p * (1+s)) ∂volume) ≤
      L ^ (p * (1+s)) * (∫⁻ x in A, ‖u x‖ₑ ^ p ∂volume) ^ s *
        ((↑(5 * 5 ^ Module.finrank ℝ (Vec d)) : ℝ≥0∞) *
          ∫⁻ x in A, ‖u x‖ₑ ^ p ∂volume) := by
  have hq : 0 < p * (1+s) := by positivity
  have hf : AEMeasurable (fun x => ‖u x‖ₑ ^ p) volume :=
    hu.aemeasurable.enorm.pow_const p
  apply c9_parabolic_separated_slab_moment_transport d T U r hr htsep hsep A D hA
    hcontain hcover (fun x => ‖u x‖ₑ ^ p) (fun x => ‖u x‖ₑ ^ (p * (1+s)))
    hf s hs (L ^ (p * (1+s)))
  intro t ht y hy
  have hg := hlocal t ht y hy
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top
      (hu.mono_measure Measure.restrict_le_self),
    eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
      (hu.mono_measure Measure.restrict_le_self),
    ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hp.le] at hg
  have hb := ENNReal.rpow_le_rpow hg hq.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hb
  have hq' : (1 / (p * (1+s))) * (p * (1+s)) = 1 := by
    field_simp [ne_of_gt hq]
  have hp' : (1 / p) * (p * (1+s)) = s + 1 := by
    field_simp [ne_of_gt hp]; ring
  rw [hq', hp', ENNReal.rpow_one,
    ENNReal.rpow_add_of_nonneg _ _ hs (by norm_num), ENNReal.rpow_one] at hb
  simpa only [mul_assoc] using hb

end EinsteinFull.Calculus
