import EinsteinFull.Calculus.C5TubePositiveConcentricGain

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The early and late trace intervals lie inside the canonical outer cylinder,
with the late interval strictly after the support of the time cutoff. -/
theorem b_positive_nested_trace_intervals (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1) :
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    0 < δ ∧ a < a + δ / 2 ∧ b - δ < b - δ / 2 ∧
      a + δ / 2 ≤ b - δ ∧
      Set.Ioo a (a + δ / 2) ⊆ Set.Ioo a b ∧
      Set.Ioo (b - δ) (b - δ / 2) ⊆ Set.Ioo a b := by
  dsimp only
  have hδ : 0 < (σ - σ') / 8 := by linarith
  have hsep : -3 / 4 - (σ - 1 / 2) / 4 + (σ - σ') / 8 / 2 ≤
      -1 / 2 + (σ - 1 / 2) / 4 - (σ - σ') / 8 := by linarith
  refine ⟨hδ, by linarith, by linarith, hsep, ?_, ?_⟩
  · intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 (by linarith [hsep])⟩
  · intro t ht
    exact ⟨lt_of_le_of_lt (by linarith [hsep]) ht.1, by linarith [ht.2]⟩

/-- The canonical spatial cutoff has the squared Euclidean gradient bound
needed for the selected-trace estimate. -/
theorem b_positive_nested_spatial_gradient (d : ℕ) (σ' σ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) :
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤
      (64 / (σ - σ')) ^ 2 := by
  dsimp only
  have hr : 0 ≤ 1 / 2 + (σ' - 1 / 2) / 2 := by linarith
  have hrR : 1 / 2 + (σ' - 1 / 2) / 2 < 1 / 2 + (σ - 1 / 2) / 2 := by linarith
  intro x
  have hb := PDE.canonicalBallCutoff_gradient_bound (x₀ := (0 : Vec d)) hr hrR x
  have hs := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hb 2
  rw [PDE.vecEuclideanNorm_sq] at hs
  have hgap : (1 / 2 + (σ - 1 / 2) / 2) -
      (1 / 2 + (σ' - 1 / 2) / 2) = (σ - σ') / 2 := by ring
  rw [hgap] at hs
  have heq : 32 / ((σ - σ') / 2) = 64 / (σ - σ') := by
    have hn : σ - σ' ≠ 0 := ne_of_gt (sub_pos.mpr hσ)
    field_simp
    <;> ring
  rw [heq] at hs
  simpa only [PDE.vecNormSq, PDE.vecDot, euclideanSq, dot,
    PDE.classicalGradient_apply, PDE.basisVec, unitVector] using hs

/-- Selected actual energy traces on the canonical outer positive cylinder. -/
theorem b_positive_nested_selected_trace (d : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (σ' σ : ℝ) (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) :
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
    ∃ (E : ℝ → ℝ) (t : ℝ), t ∈ Set.Ioo (b - δ) (b - δ / 2) ∧
      (∀ᵐ q ∂volume.restrict (Set.Ioo a b),
        E q = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (q,x) + ε) p) ∧
      ∀ q ∈ Set.Ioo a b, q < t → E q ≤
        ((δ / 2)⁻¹ + (2*p/(κ^3*(1-p))) * ((64 / (σ - σ'))^2 * κ⁻¹)) *
          (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z + ε) p) := by
  dsimp only
  let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
  let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
  let δ : ℝ := (σ - σ') / 8
  let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  have hr : 0 < r ∧ r < R ∧ R < 1 := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have hR : 0 < R := lt_trans hr.1 hr.2.1
  have hgeom := b_positive_nested_trace_intervals σ' σ hσ' hσ hσ1
  change 0 < δ ∧ a < a + δ / 2 ∧ b - δ < b - δ / 2 ∧
      a + δ / 2 ≤ b - δ ∧ Set.Ioo a (a + δ / 2) ⊆ Set.Ioo a b ∧
      Set.Ioo (b - δ) (b - δ / 2) ⊆ Set.Ioo a b at hgeom
  have hab : a < b := by dsimp [a, b]; linarith
  have htime : Set.Ioo a b ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    dsimp [a, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hspace : sourceBall (0 : Vec d) R ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < R at hx
    change euclideanNorm (x - 0) < 1
    exact lt_trans hx hr.2.2
  have hχs : tsupport χ ⊆ sourceBall (0 : Vec d) R := by
    rw [c8_sourceBall_eq_euclideanBall (0 : Vec d) hR]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer hr.1.le hr.2.1
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu hε
  have hcal' := c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet htime hspace hshift
  have hpos' := ae_restrict_of_ae_restrict_of_subset (Set.prod_mono htime hspace) hpos
  obtain ⟨E, s, t, hs, ht, hsE, htE, hrep, henergy, hback, htrace, hst, hgrad⟩ :=
    c5_positive_power_cutoff_selected_traces hκ hR hab hε hp hp1
      hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1 hgeom.2.2.2.2.2
      ρ α hell (fun z => u z + ε) G hcal' hpos' χ
      (PDE.canonicalBallCutoff_smooth 0 hr.1.le hr.2.1)
      (PDE.canonicalBallCutoff_hasCompactSupport hr.1.le hr.2.1) hχs
      (PDE.canonicalBallCutoff_nonneg _ _ _) (PDE.canonicalBallCutoff_le_one _ _ _)
      (64 / (σ - σ')) (b_positive_nested_spatial_gradient d σ' σ hσ' hσ)
  refine ⟨E, t, ht, hrep, ?_⟩
  intro q hq hqt
  have h := htrace q hq hqt
  have heq : (b - δ / 2) - (b - δ) = δ / 2 := by ring
  rw [heq] at h
  exact h

/-- The selected-trace factor has a uniform inverse-square gap bound. -/
theorem b_positive_nested_trace_factor (κ σ' σ p : ℝ)
    (hκ : 0 < κ) (hσ' : 1 / 2 ≤ σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1)
    (hp : 0 < p) (hpHalf : p < 1 / 2) :
    (((σ - σ') / 8 / 2)⁻¹ +
      (2*p/(κ^3*(1-p))) * ((64 / (σ - σ'))^2 * κ⁻¹)) ≤
      (16 + 8192 * κ⁻¹ ^ 4) / (σ - σ') ^ 2 := by
  have hg : 0 < σ - σ' := sub_pos.mpr hσ
  have hg1 : σ - σ' ≤ 1 := by linarith
  have hpbound : 2*p / (1-p) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-p)).2
    linarith
  have heq1 : ((σ - σ') / 8 / 2)⁻¹ = 16 / (σ - σ') := by
    field_simp
    <;> norm_num
  have heq2 : (2*p/(κ^3*(1-p))) * ((64 / (σ - σ'))^2 * κ⁻¹) =
      (2*p/(1-p)) * (4096 * κ⁻¹ ^ 4 / (σ - σ') ^ 2) := by
    field_simp
    <;> ring
  rw [heq1, heq2]
  have hn : 0 ≤ 4096 * κ⁻¹ ^ 4 / (σ - σ') ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_right hpbound hn
  have hfirst : 16 / (σ - σ') ≤ 16 / (σ - σ') ^ 2 := by
    apply (div_le_div_iff₀ hg (sq_pos_of_pos hg)).2
    nlinarith [sq_nonneg (σ - σ')]
  calc
    _ ≤ 16 / (σ - σ') ^ 2 + 2 * (4096 * κ⁻¹ ^ 4 / (σ - σ') ^ 2) := add_le_add hfirst hm
    _ = _ := by ring

/-- A time factor pulls out of the real-valued positive-power slice integral. -/
theorem b_positive_slice_factor_identity {d : ℕ} {R a b ε p : ℝ}
    (ρ : Vec d → ℝ) (u : ℝ × Vec d → ℝ) (χ : Vec d → ℝ)
    (θ : ℝ → ℝ) (E : ℝ → ℝ)
    (hR : sourceBall (0 : Vec d) R ⊆ sourceBall 0 1)
    (hχ : tsupport χ ⊆ sourceBall (0 : Vec d) R)
    (hpos : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R),
      0 ≤ u z + ε)
    (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x) + ε) p) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * ((θ t * χ x) * Real.rpow (u (t,x) + ε) (p / 2)) ^ 2) = θ t ^ 2 * E t := by
  have hpos' := hpos
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hpos'
  have hslices := Measure.ae_ae_of_ae_prod hpos'
  filter_upwards [hslices, hrep] with t ht hEt
  rw [hEt]
  have hext : (∫ x in sourceBall (0 : Vec d) 1,
      ρ x * ((θ t * χ x) * Real.rpow (u (t,x) + ε) (p / 2)) ^ 2) =
      ∫ x in sourceBall (0 : Vec d) R,
      ρ x * ((θ t * χ x) * Real.rpow (u (t,x) + ε) (p / 2)) ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet hR
    intro x hx
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx.2 (hχ h))
    simp [hz]
  rw [hext, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  have hpwr : Real.rpow (u (t,x) + ε) (p / 2) ^ 2 = Real.rpow (u (t,x) + ε) p := by
    change ((u (t,x) + ε) ^ (p / 2) : ℝ) ^ (2 : ℕ) =
      ((u (t,x) + ε) ^ p : ℝ)
    rw [← Real.rpow_mul_natCast hx]
    congr 1
    ring
  rw [mul_pow, mul_pow, hpwr]
  ring

/-- Uniform real-valued time-slice estimate for the canonical nested cutoff. -/
theorem b_positive_nested_slice_trace_weighted (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C m : ℝ, 0 < C ∧ 0 < m ∧ ∀ σ' σ : ℝ,
    1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ ε p : ℝ, 0 < ε → 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * (η (t,x) * Real.rpow (u (t,x) + ε) (p / 2)) ^ 2) ≤
      (C * Real.rpow (σ - σ') (-m)) *
        (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z + ε) p) := by
  refine ⟨16 + 8192 * κ⁻¹ ^ 4, 2, by positivity, by norm_num, ?_⟩
  intro σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp hpRange
  dsimp only
  let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
  let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
  let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
  let δ : ℝ := (σ - σ') / 8
  let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : Vec d) r R
  let θ : ℝ → ℝ := fun t =>
    PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) t *
      PDE.Parabolic.LocalMax.timeRamp (b - δ) δ t
  let M : ℝ := ∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
    ρ z.2 * Real.rpow (u z + ε) p
  let D : ℝ := (16 + 8192 * κ⁻¹ ^ 4) / (σ - σ') ^ 2
  have hgap : 0 < σ - σ' := sub_pos.mpr hσ
  have hr : 0 < r ∧ r < R ∧ R < 1 := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have hR : 0 < R := lt_trans hr.1 hr.2.1
  have hgaps := c5_positive_concentric_time_gaps σ' σ hσ' hσ hσ1
  change 0 < δ ∧ -1 < a + δ ∧ a + δ < a' ∧
    (-1 / 2 + (σ' - 1 / 2) / 4 : ℝ) ≤ (b - δ) - δ ∧ b - δ < 1 at hgaps
  have htime : Set.Ioo a b ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    dsimp [a, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hspace : sourceBall (0 : Vec d) R ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < R at hx
    change euclideanNorm (x - 0) < 1
    exact lt_trans hx hr.2.2
  have hχs : tsupport χ ⊆ sourceBall (0 : Vec d) R := by
    rw [c8_sourceBall_eq_euclideanBall (0 : Vec d) hR]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer hr.1.le hr.2.1
  have hpos : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), 0 ≤ u z + ε := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Set.prod_mono htime hspace) hu] with z hz
    linarith
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1) (Real.rpow_nonneg hz _)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpHalf := c5_positive_gain_exponent_lt_half d hd p hpRange
  obtain ⟨E, t, ht, hrep, htrace⟩ := b_positive_nested_selected_trace d κ hκ
    σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp (by linarith)
  have hid := b_positive_slice_factor_identity ρ u χ θ E hspace hχs hpos hrep
  have hid' := (ae_restrict_iff' measurableSet_Ioo).mp hid
  have hfactor := b_positive_nested_trace_factor κ σ' σ p hκ hσ' hσ hσ1 hp hpHalf
  have hθ0 (q : ℝ) : 0 ≤ θ q := by
    exact mul_nonneg (Real.smoothTransition.nonneg _)
      (PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _)
  have hθ1 (q : ℝ) : θ q ≤ 1 := by
    exact (mul_le_mul (Real.smoothTransition.le_one _)
      (PDE.Parabolic.LocalMax.timeRamp_le_one _ _ _)
      (PDE.Parabolic.LocalMax.timeRamp_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)
  have hθearly (q : ℝ) (hq : q ≤ a) : θ q = 0 := by
    have hh : 0 < (a' - (a + δ)) / 2 := by linarith [hgaps.2.2.1]
    have hz : PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) q = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hgaps.1]) hh.le
    simp [θ, hz]
  have hθlate (q : ℝ) (hq : b - δ ≤ q) : θ q = 0 := by
    simp [θ, PDE.Parabolic.LocalMax.timeRamp_eq_zero hgaps.1 hq]
  have hDform : (16 + 8192 * κ⁻¹ ^ 4) * Real.rpow (σ - σ') (-(2 : ℝ)) = D := by
    change (16 + 8192 * κ⁻¹ ^ 4) * (σ - σ') ^ (-(2 : ℝ)) = D
    rw [Real.rpow_neg hgap.le]
    norm_num only [Real.rpow_ofNat]
    simp only [D, div_eq_mul_inv]
  rw [hDform]
  filter_upwards [ae_restrict_of_ae hid'] with q hq
  by_cases hqouter : q ∈ Set.Ioo a b
  · by_cases hqearly : q < b - δ
    · have hqt : q < t := lt_trans hqearly ht.1
      have hbound : E q ≤ D * M := (htrace q hqouter hqt).trans
        (mul_le_mul_of_nonneg_right hfactor hM)
      have hsquare : θ q ^ 2 ≤ 1 := by nlinarith [hθ0 q, hθ1 q, sq_nonneg (θ q)]
      change (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * ((θ q * χ x) * Real.rpow (u (q,x) + ε) (p / 2)) ^ 2) ≤ D * M
      rw [hq hqouter]
      exact (mul_le_mul_of_nonneg_left hbound (sq_nonneg _)).trans
        (by nlinarith [mul_nonneg hD hM])
    · have hz := hθlate q (le_of_not_gt hqearly)
      change (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * ((θ q * χ x) * Real.rpow (u (q,x) + ε) (p / 2)) ^ 2) ≤ D * M
      simp [hz, mul_nonneg hD hM]
  · have hz : θ q = 0 := by
      by_cases hqa : q ≤ a
      · exact hθearly q hqa
      · exact hθlate q (by have : b ≤ q := le_of_not_gt (fun h => hqouter ⟨lt_of_not_ge hqa, h⟩); linarith [hgaps.1])
    change (∫ x in sourceBall (0 : Vec d) 1,
      ρ x * ((θ q * χ x) * Real.rpow (u (q,x) + ε) (p / 2)) ^ 2) ≤ D * M
    simp [hz, mul_nonneg hD hM]

/-- The same slice estimate with the unweighted outer mass. -/
theorem b_positive_nested_slice_trace (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C m : ℝ, 0 < C ∧ 0 < m ∧ ∀ σ' σ : ℝ,
    1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ ε p : ℝ, 0 < ε → 0 < p → p ≤ (d : ℝ) / (2 * ((d : ℝ) + 2)) →
    let r : ℝ := 1 / 2 + (σ' - 1 / 2) / 2
    let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
    let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
    let a' : ℝ := -3 / 4 - (σ' - 1 / 2) / 4
    let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
    let δ : ℝ := (σ - σ') / 8
    let η : ℝ × Vec d → ℝ := fun z =>
      (PDE.Parabolic.LocalMax.cylTimeRamp (a + δ) ((a' - (a + δ)) / 2) z.1 *
        PDE.Parabolic.LocalMax.timeRamp (b - δ) δ z.1) *
          PDE.canonicalBallCutoff (0 : Vec d) r R z.2
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      (∫ x in sourceBall (0 : Vec d) 1,
        ρ x * (η (t,x) * Real.rpow (u (t,x) + ε) (p / 2)) ^ 2) ≤
      (C * Real.rpow (σ - σ') (-m)) *
        (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, Real.rpow (u z + ε) p) := by
  obtain ⟨C, m, hC, hm, hweighted⟩ := b_positive_nested_slice_trace_weighted d hd κ hκ
  refine ⟨C * κ⁻¹, m, by positivity, hm, ?_⟩
  intro σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp hpRange
  dsimp only
  let R : ℝ := 1 / 2 + (σ - 1 / 2) / 2
  let a : ℝ := -3 / 4 - (σ - 1 / 2) / 4
  let b : ℝ := -1 / 2 + (σ - 1 / 2) / 4
  have hr := c5_positive_concentric_radius_bounds σ' σ hσ' hσ hσ1
  have htime : Set.Ioo a b ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    dsimp [a, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hspace : sourceBall (0 : Vec d) R ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < R at hx
    change euclideanNorm (x - 0) < 1
    exact lt_trans hx hr.2.2
  obtain ⟨hshift, hpos⟩ := c8_weighted_caloric_positive_shift hκ hell hcal hu hε
  have hcal' := c11_weighted_caloric_cylinder_mono measurableSet_Ioo measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet htime hspace hshift
  have hpos' := ae_restrict_of_ae_restrict_of_subset (Set.prod_mono htime hspace) hpos
  have hp1 : p < 1 := by have h := c5_positive_gain_exponent_lt_half d hd p hpRange; linarith
  have hi := c13_positive_power_integrable hε hp hp1 ρ α (fun z => u z + ε) G hcal' hpos'
  have hiw := c13_weighted_positive_power_integrable hκ hε hp hp1 ρ α hell
    (fun z => u z + ε) G hcal' hpos'
  have hmass : (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      ρ z.2 * Real.rpow (u z + ε) p) ≤
      κ⁻¹ * ∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, Real.rpow (u z + ε) p := by
    rw [← integral_const_mul]
    apply integral_mono_ae hiw (hi.const_mul κ⁻¹)
    filter_upwards [hpos'] with z hz
    exact mul_le_mul_of_nonneg_right (hell.2.2 z.2).2.1
      (Real.rpow_nonneg (le_trans hε.le hz) p)
  have hbound := hweighted σ' σ hσ' hσ hσ1 ρ α hell u G hcal hu ε p hε hp hpRange
  have hfactor : 0 ≤ C * Real.rpow (σ - σ') (-m) :=
    mul_nonneg hC.le (Real.rpow_nonneg (sub_pos.mpr hσ).le _)
  filter_upwards [hbound] with t ht
  exact ht.trans ((mul_le_mul_of_nonneg_left hmass hfactor).trans_eq (by ring))

end EinsteinFull.Calculus


