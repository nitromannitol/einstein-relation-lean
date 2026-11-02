import EinsteinFull.Calculus.U7RegularKernelDensity
import EinsteinFull.Calculus.U8RegularKernelMoments
import EinsteinFull.Calculus.U8RegularUnforcedExponential
import EinsteinFull.Calculus.U5RegularGaugeGrowth
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import SubdiffusiveProcess.Processes.FellerRealizationRestart

open MeasureTheory ProbabilityTheory
open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

open Blueprint EinsteinRelation.SpatialDirichlet
open Filter Set Topology NormedSpace MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

/-- Cutoff errors vanish with the dilation while the growth coefficient is
explicitly linear in the derivative bounds, uniformly in the test. -/
theorem u8_regular_cutoff_product_quantitative {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (h : Vec d → ℝ) (H : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ H →
      (∀ x, 0 ≤ h x ∧ h x ≤ H) →
      (∀ x j, |fderiv ℝ h x (unitVector j)| ≤ A * h x) →
      (∀ x i j, |fderiv ℝ (fun y => fderiv ℝ h y (unitVector j)) x
        (unitVector i)| ≤ B * h x) →
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ c : ℝ, 0 < c → c ≤ 1 →
        |physicalGenerator (firstCoordinateIndex hd) ω lam
          (fun z => χ (c • z) * h z) x| ≤
          (C₁ * A + C₂ * B) * (χ (c • x) * h x) + c * (E * H) := by
  obtain ⟨M, hM, hder⟩ := u5_dilated_cutoff_derivative_bound hχ hc
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro A B hA hB
  refine ⟨C₁ * M + C₂ * (M + 2 * M * A), by positivity, ?_⟩
  intro h H hh hH hbound hfirst hsecond
  filter_upwards [hgen] with x hx
  intro c hc0 hc1
  let f : Vec d → ℝ := fun z => χ (c • z)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hχ.comp (contDiff_const_smul c)
  have hf0 : 0 ≤ f x := (hχ01 (c • x)).1
  have hf1 : f x ≤ 1 := (hχ01 (c • x)).2
  have hh0 : 0 ≤ h x := (hbound x).1
  have hhH : h x ≤ H := (hbound x).2
  have hprod : 0 ≤ f x * h x := mul_nonneg hf0 hh0
  have hD : 0 ≤ c * M := mul_nonneg hc0.le hM
  have hfirst' (i : Fin d) :
      |fderiv ℝ (fun z => f z * h z) x (unitVector i)| ≤
        A * (f x * h x) + c * (M * H) := by
    rw [(gmpPhysical_coordinate_product_derivatives f h hf hh x i i).1]
    have hf' := (hder c hc0 hc1 x i i).1
    change |fderiv ℝ f x (unitVector i)| ≤ c * M at hf'
    have ha := hfirst x i
    have hfa : |fderiv ℝ f x (unitVector i) * h x| ≤ (c * M) * H := by
      rw [abs_mul, abs_of_nonneg hh0]
      exact mul_le_mul hf' hhH hh0 hD
    have hfb : |f x * fderiv ℝ h x (unitVector i)| ≤ f x * (A * h x) := by
      rw [abs_mul, abs_of_nonneg hf0]
      exact mul_le_mul_of_nonneg_left ha hf0
    have := (abs_add_le _ _).trans (add_le_add hfa hfb)
    nlinarith
  have hsecond' (i j : Fin d) :
      |fderiv ℝ (fun y => fderiv ℝ (fun z => f z * h z) y (unitVector j)) x
        (unitVector i)| ≤ B * (f x * h x) + c * (M * H + 2 * M * (A * H)) := by
    rw [(gmpPhysical_coordinate_product_derivatives f h hf hh x i j).2]
    have hfi := (hder c hc0 hc1 x i j).1
    have hfj := (hder c hc0 hc1 x j i).1
    have hfij := (hder c hc0 hc1 x i j).2
    change |fderiv ℝ f x (unitVector j)| ≤ c * M at hfi
    change |fderiv ℝ f x (unitVector i)| ≤ c * M at hfj
    change |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)| ≤ c * M at hfij
    have hhj : |fderiv ℝ h x (unitVector j)| ≤ A * H :=
      (hfirst x j).trans (mul_le_mul_of_nonneg_left hhH hA)
    have hhi : |fderiv ℝ h x (unitVector i)| ≤ A * H :=
      (hfirst x i).trans (mul_le_mul_of_nonneg_left hhH hA)
    have h1 : |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * h x| ≤ (c * M) * H := by
      rw [abs_mul, abs_of_nonneg hh0]
      exact mul_le_mul hfij hhH hh0 hD
    have h2 : |fderiv ℝ f x (unitVector j) * fderiv ℝ h x (unitVector i)| ≤ (c * M) * (A * H) := by
      rw [abs_mul]
      exact mul_le_mul hfi hhi (abs_nonneg _) hD
    have h3 : |fderiv ℝ f x (unitVector i) * fderiv ℝ h x (unitVector j)| ≤ (c * M) * (A * H) := by
      rw [abs_mul]
      exact mul_le_mul hfj hhj (abs_nonneg _) hD
    have h4 : |f x * fderiv ℝ (fun y => fderiv ℝ h y (unitVector j)) x (unitVector i)| ≤ f x * (B * h x) := by
      rw [abs_mul, abs_of_nonneg hf0]
      exact mul_le_mul_of_nonneg_left (hsecond x i j) hf0
    have ht := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)
    nlinarith
  have h1 : 0 ≤ A * (f x * h x) + c * (M * H) := by positivity
  have h2 : 0 ≤ B * (f x * h x) + c * (M * H + 2 * M * (A * H)) := by positivity
  have hs : ContDiff ℝ 2 (fun z => f z * h z) :=
    (hf.mul hh).of_le (WithTop.coe_le_coe.2 le_top)
  have hb := hx _ hs _ _ h1 h2 hfirst' hsecond'
  convert hb using 1 <;> ring


/-- Quantitative cutoff resolvent comparison for all coordinate tilts. -/
theorem u8_regular_cutoff_resolvent_quantitative {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (q : ℝ) (k : Fin d),
      ∃ E : ℝ, 0 ≤ E ∧ ∀ (a : ℝ) (ha : 0 < a)
      (c : ℝ) (hc0 : 0 < c), c ≤ 1 → ∀ (α : ℝ) (hα : 0 < α) x,
        let φ := u5CutoffBoundedCoordinateTest χ hχ hc a q ha k c hc0
        (α - (C₁ * |q| + C₂ * q ^ 2)) *
          u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x ≤
          φ x + c * (E * a⁻¹ + 1) / α := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    u8_regular_cutoff_product_quantitative hd ω lam Λ hΛ hω hχ hc hχ01
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro q k
  obtain ⟨E, hE, hu⟩ := hgen |q| (q ^ 2) (abs_nonneg q) (sq_nonneg q)
  refine ⟨E, hE, ?_⟩
  intro a ha c hc0 hc1 α hα x
  let φ := u5CutoffBoundedCoordinateTest χ hχ hc a q ha k c hc0
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => χ (c • x) * u5BoundedExp a (q * x k))
    exact (hχ.comp (contDiff_const_smul c)).mul (u5_bounded_coordinate_exp_properties a q ha k).1
  have hφc : HasCompactSupport φ := by
    change HasCompactSupport (fun x => χ (c • x) * u5BoundedExp a (q * x k))
    exact (hc.comp_smul (ne_of_gt hc0)).mul_right
  have hB : 0 < c * (E * a⁻¹ + 1) := by positivity
  have hp := u5_bounded_coordinate_exp_properties a q ha k
  have hgen' := hu _ _ hp.1 (inv_nonneg.mpr ha.le) hp.2.1 hp.2.2.1 hp.2.2.2
  have haegen : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ x -
        (C₁ * |q| + C₂ * q ^ 2) * φ x ≤ c * (E * a⁻¹ + 1) := by
    apply (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mpr
    filter_upwards [hgen'] with y hy
    have hh := hy c hc0 hc1
    change |physicalGenerator (firstCoordinateIndex hd) ω lam φ y| ≤
      (C₁ * |q| + C₂ * q ^ 2) * φ y + c * (E * a⁻¹) at hh
    have hl := le_abs_self (physicalGenerator (firstCoordinateIndex hd) ω lam φ y)
    nlinarith
  exact u5_regular_resolvent_compactTest_upper hd ω lam Λ hΛ hω φ hφ hφc
    (C₁ * |q| + C₂ * q ^ 2) (c * (E * a⁻¹ + 1)) hB haegen α hα x

/-- The explicit tilt bound survives removal of the spatial cutoff for compact tests. -/
theorem u8_regular_compact_resolvent_quantitative {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (q : ℝ) (k : Fin d),
      ∀ (a : ℝ) (_ha : 0 < a)
      (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
      (_hfc : HasCompactSupport (f : Vec d → ℝ))
      (_hf : ∀ x, f x ≤ u5BoundedExp a (q * x k))
      (α : ℝ) (hα : 0 < α), (C₁ * |q| + C₂ * q ^ 2) < α → ∀ x,
      (α - (C₁ * |q| + C₂ * q ^ 2)) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x ≤
        u5BoundedExp a (q * x k) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hcut⟩ :=
    u8_regular_cutoff_resolvent_quantitative hd ω lam Λ hΛ hω hχ hc hχ01
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro q k
  obtain ⟨E, hE, hres⟩ := hcut q k
  let C := C₁ * |q| + C₂ * q ^ 2
  intro a ha f hfc hf α hα hαC x
  obtain ⟨δ, hδ, hδ1, hdom⟩ :=
    u5_cutoff_bounded_coordinate_dominates_compact hχ hc hχone
      (fun y => (hχ01 y).1) a q ha k f hfc hf
  let D := E * a⁻¹ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  let c := min δ (ε * α / (2 * D))
  have hc0 : 0 < c := lt_min hδ (by positivity)
  have hcδ : c ≤ δ := min_le_left _ _
  have hc1 : c ≤ 1 := hcδ.trans hδ1
  let φ := u5CutoffBoundedCoordinateTest χ hχ hc a q ha k c hc0
  have hcmp : ∀ y, f y ≤ φ y := hdom c hc0 hcδ
  have hR : u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x ≤
      u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x := by
    have hp := u2_regular_c0_resolvent_positive hd ω lam Λ hΛ hω α hα (φ - f)
      (fun y => by change 0 ≤ φ y - f y; linarith [hcmp y]) x
    rw [map_sub] at hp
    change 0 ≤ u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x -
      u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x at hp
    linarith
  have hφ : φ x ≤ u5BoundedExp a (q * x k) := by
    change χ (c • x) * u5BoundedExp a (q * x k) ≤ _
    nlinarith [(hχ01 (c • x)).2, (u5_bounded_exp_bounds a ha (q * x k)).1]
  have he : c * D / α ≤ ε := by
    have hcε : c ≤ ε * α / (2 * D) := min_le_right _ _
    have hm : c * (2 * D) ≤ ε * α := (le_div_iff₀ (by positivity)).mp hcε
    apply (div_le_iff₀ hα).2
    nlinarith [mul_nonneg hc0.le hD.le]
  have hr := hres a ha c hc0 hc1 α hα x
  change (α - C) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα φ x ≤
    φ x + c * D / α at hr
  have hm := mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hαC.le)
  linarith


/-- The explicit tilt bound extends to all dominated continuous tests vanishing at infinity. -/
theorem u8_regular_resolvent_quantitative {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (q : ℝ) (k : Fin d),
      ∀ (a : ℝ) (_ha : 0 < a)
      (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
      (_hf : ∀ x, f x ≤ u5BoundedExp a (q * x k))
      (α : ℝ) (hα : 0 < α), (C₁ * |q| + C₂ * q ^ 2) < α → ∀ x,
      (α - (C₁ * |q| + C₂ * q ^ 2)) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x ≤
        u5BoundedExp a (q * x k) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hres⟩ := u8_regular_compact_resolvent_quantitative
    hd ω lam Λ hΛ hω hχ hc hχone hχ01
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro q k
  let C := C₁ * |q| + C₂ * q ^ 2
  intro a ha f hf α hα hαC x
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Filter.Tendsto ε Filter.atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose g hgc hgb hgK hga using fun n : ℕ =>
    gmpC0_exists_bounded_compact_cutoff f ∅ isCompact_empty (hε n)
  let fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ := fun n => f * g n
  have hb (n : ℕ) : ‖fn n - f‖ ≤ ε n := by
    change ‖(fn n - f).toBCF‖ ≤ ε n
    apply (BoundedContinuousFunction.norm_le (le_of_lt (hε n))).2
    intro y
    change ‖(f * g n) y - f y‖ ≤ ε n
    simpa only [Real.norm_eq_abs] using hga n y
  have hconv : Filter.Tendsto fn Filter.atTop (𝓝 f) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hb hεlim
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
  have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
    (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
  have hlim : Filter.Tendsto (fun n => (α - C) * R (fn n) x) Filter.atTop
      (𝓝 ((α - C) * R f x)) :=
    ((heval.tendsto (R f)).comp (R.continuous.tendsto f |>.comp hconv)).const_mul _
  apply le_of_tendsto' hlim
  intro n
  apply hres q k a ha (fn n) (HasCompactSupport.mul_left (hgc n)) ?_ α hα hαC x
  intro y
  change f y * g n y ≤ u5BoundedExp a (q * y k)
  have hp := (u5_bounded_exp_bounds a ha (q * y k)).1
  have hg := hgb n y
  nlinarith [mul_nonneg (sub_nonneg.mpr hg.2) hp,
    mul_nonneg (sub_nonneg.mpr (hf y)) hg.1]


/-- The explicit tilt bound propagates through iterated normalized resolvents. -/
theorem u8_regular_resolvent_pow_quantitative {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (q : ℝ) (k : Fin d), ∀ (a : ℝ), 0 < a →
      ∀ (f : ZeroAtInftyContinuousMap (Vec d) ℝ),
      (∀ x, f x ≤ u5BoundedExp a (q * x k)) →
      ∀ (α : MarkovProcess.Semigroup.PositiveShift), (C₁ * |q| + C₂ * q ^ 2) < (α : ℝ) → ∀ n x,
      (((u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω).scaledOperator α) ^ n) f x ≤
        ((α : ℝ) / ((α : ℝ) - (C₁ * |q| + C₂ * q ^ 2))) ^ n * u5BoundedExp a (q * x k) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hres⟩ := u8_regular_resolvent_quantitative
    hd ω lam Λ hΛ hω hχ hc hχone hχ01
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro q k
  let C := C₁ * |q| + C₂ * q ^ 2
  intro a ha f hf α hαC
  have hden : 0 < (α : ℝ) - C := sub_pos.mpr hαC
  apply u5_operator_pow_below_barrier _ _ _ (div_pos α.property hden) ?_ f hf
  intro g hg x
  have hr := hres q k a ha g hg α α.property hαC x
  change (α : ℝ) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α α.property g x ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith [mul_le_mul_of_nonneg_left hr α.property.le]


/-- The regular physical semigroup preserves the quantitative exponential barrier. -/
theorem u8_regular_semigroup_quantitative {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (q : ℝ) (k : Fin d), ∀ (a : ℝ), 0 < a →
      ∀ (f : C₀(Vec d, ℝ)), (∀ x, f x ≤ u5BoundedExp a (q * x k)) →
      ∀ (t : ℝ≥0) x, u2RegularC0Semigroup hd ω lam Λ hΛ hω t f x ≤
        Real.exp ((C₁ * |q| + C₂ * q ^ 2) * (t : ℝ)) * u5BoundedExp a (q * x k) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hpow⟩ := u8_regular_resolvent_pow_quantitative
    hd ω lam Λ hΛ hω hχ hc hχone hχ01
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro q k
  let C := C₁ * |q| + C₂ * q ^ 2
  intro a ha f hf t x
  exact u5_generated_semigroup_below_barrier
    (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω) C
    (fun y => u5BoundedExp a (q * y k)) f (hpow q k a ha f hf) t x


/-- The physical kernel integrates each bounded exponential barrier with quantitative growth. -/
theorem u8_regular_kernel_bounded_quantitative {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχone : ∀ y, ‖y‖ ≤ 1 → χ y = 1) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (q : ℝ) (k : Fin d), ∀ (a : ℝ), 0 < a → ∀ (t : ℝ≥0) x,
      (∫ y, u5BoundedExp a (q * y k)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      Real.exp ((C₁ * |q| + C₂ * q ^ 2) * (t : ℝ)) * u5BoundedExp a (q * x k) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hsem⟩ := u8_regular_semigroup_quantitative
    hd ω lam Λ hΛ hω hχ hc hχone hχ01
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro q k
  let C := C₁ * |q| + C₂ * q ^ 2
  intro a ha t x
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsFiniteMeasure (P t x) :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  let c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hcpos (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  have hclim : Tendsto c atTop (𝓝 0) := by
    simpa [c] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let f : ℕ → C₀(Vec d, ℝ) := fun n =>
    u5CutoffBoundedCoordinateTest χ hχ hc a q ha k (c n) (hcpos n)
  have hχzero : χ 0 = 1 := hχone 0 (by simp)
  have hpoint (y : Vec d) : Tendsto (fun n => f n y) atTop
      (𝓝 (u5BoundedExp a (q * y k))) := by
    have hsmul : Tendsto (fun n => c n • y) atTop (𝓝 (0 : Vec d)) := by
      simpa using hclim.smul (tendsto_const_nhds (x := y))
    have hlim := (hχ.continuous.tendsto 0).comp hsmul
    have hh := hlim.mul_const (u5BoundedExp a (q * y k))
    change Tendsto (fun n => χ (c n • y) * u5BoundedExp a (q * y k)) atTop _
    simpa [hχzero] using hh
  have hbounded (n : ℕ) (y : Vec d) : 0 ≤ f n y ∧ f n y ≤ a⁻¹ := by
    change 0 ≤ χ (c n • y) * u5BoundedExp a (q * y k) ∧
      χ (c n • y) * u5BoundedExp a (q * y k) ≤ a⁻¹
    have hcut := hχ01 (c n • y)
    have hb := u5_bounded_exp_bounds a ha (q * y k)
    constructor
    · exact mul_nonneg hcut.1 hb.1
    · nlinarith [mul_nonneg (sub_nonneg.mpr hcut.2) hb.1]
  have hlim : Tendsto (fun n => ∫ y, f n y ∂P t x) atTop
      (𝓝 (∫ y, u5BoundedExp a (q * y k) ∂P t x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => a⁻¹)
    · intro n
      exact (f n).continuous.measurable.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbounded n y).1]
        exact (hbounded n y).2
    · exact Filter.Eventually.of_forall hpoint
  apply le_of_tendsto' hlim
  intro n
  rw [u2RegularC0KernelSemigroup_integral]
  apply hsem q k a ha (f n) ?_ t x
  intro y
  change χ (c n • y) * u5BoundedExp a (q * y k) ≤ u5BoundedExp a (q * y k)
  have hcut := hχ01 (c n • y)
  have hb := (u5_bounded_exp_bounds a ha (q * y k)).1
  nlinarith [mul_nonneg (sub_nonneg.mpr hcut.2) hb]


/-- The physical kernel integrates unbounded coordinate exponentials with quantitative growth. -/
theorem u8_regular_kernel_exp_quantitative {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (q : ℝ) (k : Fin d) (t : ℝ≥0) x,
      (∫⁻ y, ENNReal.ofReal (Real.exp (q * y k))
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (q * x k)) * ENNReal.ofReal (Real.exp ((C₁ * |q| + C₂ * q ^ 2) * (t : ℝ))) := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb1 : ∀ y : Vec d, ‖y‖ ≤ 1 → b y = 1 := by
    intro y hy
    apply b.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_zero_right, b] using hy
  have hb01 : ∀ y : Vec d, 0 ≤ b y ∧ b y ≤ 1 := fun _ => ⟨b.nonneg, b.le_one⟩
  obtain ⟨C₁, C₂, hC₁, hC₂, hbound⟩ := u8_regular_kernel_bounded_quantitative
    hd ω lam Λ hΛ hω b.contDiff b.hasCompactSupport hb1 hb01
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro q k t x
  let C := C₁ * |q| + C₂ * q ^ 2
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsFiniteMeasure (P t x) :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have halim : Tendsto a atTop (𝓝 0) := by
    simpa [a] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let F : ℕ → Vec d → ℝ := fun n y => u5BoundedExp (a n) (q * y k)
  have hcont (n : ℕ) : Continuous (F n) :=
    (u5_bounded_coordinate_exp_properties (a n) q (ha n) k).1.continuous
  have hF0 (n : ℕ) (y : Vec d) : 0 ≤ F n y :=
    (u5_bounded_exp_bounds (a n) (ha n) (q * y k)).1
  have hFi (n : ℕ) : Integrable (F n) (P t x) := by
    apply (integrable_const ((a n)⁻¹)).mono' (hcont n).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n y)]
      simpa only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (ha n).le)] using
        (u5_bounded_exp_bounds (a n) (ha n) (q * y k)).2.1
  have hFle (n : ℕ) (y : Vec d) : F n y ≤ Real.exp (q * y k) := by
    change Real.exp (q * y k) / (1 + a n * Real.exp (q * y k)) ≤ _
    apply div_le_self (Real.exp_nonneg _)
    nlinarith [mul_nonneg (ha n).le (Real.exp_nonneg (q * y k))]
  have hFlim (y : Vec d) : Tendsto (fun n => F n y) atTop
      (𝓝 (Real.exp (q * y k))) := by
    have hdlim : Tendsto (fun n => 1 + a n * Real.exp (q * y k)) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (halim.mul_const (Real.exp (q * y k)))
    have hh := (tendsto_const_nhds (x := Real.exp (q * y k))).div hdlim
      (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun n : ℕ => Real.exp (q * y k) /
      (1 + a n * Real.exp (q * y k))) atTop
      (𝓝 (Real.exp (q * y k) / 1)) at hh
    simpa [F, u5BoundedExp] using hh
  have hlin (n : ℕ) : (∫⁻ y, ENNReal.ofReal (F n y) ∂P t x) ≤
      ENNReal.ofReal (Real.exp (q * x k) * Real.exp (C * (t : ℝ))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (ae_of_all _ (hF0 n))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.exp (C * (t : ℝ)) * F n x := hbound q k (a n) (ha n) t x
      _ ≤ Real.exp (C * (t : ℝ)) * Real.exp (q * x k) :=
        mul_le_mul_of_nonneg_left (hFle n x) (Real.exp_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ = ∫⁻ y, liminf (fun n => ENNReal.ofReal (F n y)) atTop ∂P t x := by
      apply lintegral_congr
      intro y
      exact ((ENNReal.continuous_ofReal.tendsto _).comp (hFlim y)).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (F n y) ∂P t x) atTop :=
      lintegral_liminf_le (fun n => (hcont n).measurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal (Real.exp (q * x k) * Real.exp (C * (t : ℝ))) := by
      have h : liminf (fun n => ∫⁻ y, ENNReal.ofReal (F n y) ∂P t x) atTop ≤
          liminf (fun _ : ℕ => ENNReal.ofReal (Real.exp (q * x k) * Real.exp (C * (t : ℝ)))) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hlin)
      simpa only [Filter.liminf_const] using h
    _ = _ := ENNReal.ofReal_mul (Real.exp_nonneg _)


/-- Uniform quadratic coordinate exponential moments of the signed kernel. -/
theorem u8_regular_signed_uniform_coordinate_mgf
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (i : Fin d) (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (a * ((y - x) i)))
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        ENNReal.ofReal (Real.exp (C * (|a| + a ^ 2) * (t : ℝ))) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := u8_regular_kernel_exp_quantitative hd ω lam Λ hΛ hω
  let C := C₁ + C₂ + 1
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro a i t x
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  have hcoeff : C₁ * |a| + C₂ * a ^ 2 ≤ C * (|a| + a ^ 2) := by
    have h1 : C₁ ≤ C := by dsimp [C]; linarith
    have h2 : C₂ ≤ C := by dsimp [C]; linarith
    nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg a),
      mul_le_mul_of_nonneg_right h2 (sq_nonneg a)]
  calc
    (∫⁻ y, ENNReal.ofReal (Real.exp (a * ((y - x) i))) ∂μ) =
        ENNReal.ofReal (Real.exp (-a * x i)) *
          ∫⁻ y, ENNReal.ofReal (Real.exp (a * y i)) ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 1
      simp only [Pi.sub_apply]
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-a * x i)) *
        (ENNReal.ofReal (Real.exp (a * x i)) *
          ENNReal.ofReal (Real.exp ((C₁ * |a| + C₂ * a ^ 2) * (t : ℝ)))) :=
      mul_le_mul_right (hb a i t x) _
    _ = ENNReal.ofReal (Real.exp ((C₁ * |a| + C₂ * a ^ 2) * (t : ℝ))) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      simp
    _ ≤ ENNReal.ofReal (Real.exp (C * (|a| + a ^ 2) * (t : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hcoeff t.coe_nonneg

#print axioms u8_regular_signed_uniform_coordinate_mgf

/-- A uniform radial exponential bound, with the tilt retained explicitly. -/
theorem u8_regular_signed_uniform_euclidean_mgf
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ), 0 ≤ q → ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (q * euclideanNorm (y - x)))
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal ((2 * d) * Real.exp (C * (q + q ^ 2) * (t : ℝ))) := by
  obtain ⟨B, hB, hb⟩ := u8_regular_signed_uniform_coordinate_mgf hd ω lam Λ hΛ hω
  let C : ℝ := B * (d + (d : ℝ) ^ 2 + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q hq t x
  let Q : ℝ := q * d
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let F : Fin d → Bool → Vec d → ℝ≥0∞ := fun i s y =>
    ENNReal.ofReal (Real.exp ((if s then Q else -Q) * ((y - x) i)))
  have hm (i : Fin d) (s : Bool) : Measurable (F i s) :=
    (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_apply i).sub continuous_const))).measurable.ennreal_ofReal
  have hpoint (y : Vec d) : ENNReal.ofReal (Real.exp (q * euclideanNorm (y - x))) ≤
      ∑ i : Fin d, (F i true y + F i false y) := by
    obtain ⟨i, hi⟩ := c16_max_exists_coord_ge (by omega : 1 ≤ d)
      (y := y - x) (R := euclideanNorm (y - x)) le_rfl
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hnorm : q * euclideanNorm (y - x) ≤ Q * |(y - x) i| := by
      dsimp [Q]
      have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hdpos).mp hi) hq
      simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using h
    have he := (Real.exp_le_exp.mpr hnorm).trans
      (c16_max_exp_ge hQ (le_refl |(y - x) i|))
    have he' := ENNReal.ofReal_le_ofReal he
    rw [ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)] at he'
    apply he'.trans
    simpa [F] using
      (Finset.single_le_sum (f := fun j : Fin d => F j true y + F j false y)
        (fun j _ => bot_le) (Finset.mem_univ i))
  have hcoeff : B * (Q + Q ^ 2) ≤ C * (q + q ^ 2) := by
    have hi : Q + Q ^ 2 ≤ ((d : ℝ) + (d : ℝ) ^ 2 + 1) * (q + q ^ 2) := by
      dsimp [Q]
      have hd0 : (0 : ℝ) ≤ d := by positivity
      nlinarith [mul_nonneg hd0 (sq_nonneg q),
        mul_nonneg (sq_nonneg (d : ℝ)) hq, sq_nonneg q]
    simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_left hi hB.le
  have hi (i : Fin d) (s : Bool) : (∫⁻ y, F i s y ∂μ) ≤
      ENNReal.ofReal (Real.exp (C * (q + q ^ 2) * (t : ℝ))) := by
    have hh := hb (if s then Q else -Q) i t x
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ t.coe_nonneg
    cases s <;> simpa [abs_of_nonneg hQ, abs_of_nonpos (neg_nonpos.mpr hQ)] using hcoeff
  calc
    _ ≤ ∫⁻ y, ∑ i : Fin d, (F i true y + F i false y) ∂μ := lintegral_mono hpoint
    _ = ∑ i : Fin d, ((∫⁻ y, F i true y ∂μ) + (∫⁻ y, F i false y ∂μ)) := by
      rw [lintegral_finsetSum (f := fun i y => F i true y + F i false y)
        Finset.univ (fun i _ => (hm i true).add (hm i false))]
      simp_rw [lintegral_add_left (hm _ true)]
    _ ≤ ∑ _i : Fin d, (ENNReal.ofReal (Real.exp (C * (q + q ^ 2) * (t : ℝ))) +
        ENNReal.ofReal (Real.exp (C * (q + q ^ 2) * (t : ℝ)))) :=
      Finset.sum_le_sum fun i _ => add_le_add (hi i true) (hi i false)
    _ = _ := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (d : ℝ))]
      congr 1 <;> ring

#print axioms u8_regular_signed_uniform_euclidean_mgf

/-- A single coefficient controls the generator of every bounded coordinate
exponential, uniformly in its tilt and truncation parameter. -/
theorem u8_regular_uniform_bounded_coordinate_generator
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ (q : ℝ) (i : Fin d) (a : ℝ), 0 < a →
        |physicalGenerator (firstCoordinateIndex hd) ω lam
          (fun y => u5BoundedExp a (q * y i)) x| ≤
          C * (|q| + q ^ 2) * u5BoundedExp a (q * x i) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  let C := C₁ + C₂ + 1
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  filter_upwards [hgen] with x hx
  intro q i a ha
  have hp := u5_bounded_coordinate_exp_properties a q ha i
  have h0 := (hp.2.1 x).1
  have h := hx _ (hp.1.of_le (WithTop.coe_le_coe.2 le_top))
    (|q| * u5BoundedExp a (q * x i))
    (q ^ 2 * u5BoundedExp a (q * x i))
    (mul_nonneg (abs_nonneg q) h0) (mul_nonneg (sq_nonneg q) h0)
    (hp.2.2.1 x) (hp.2.2.2 x)
  apply h.trans
  have hc1 : C₁ ≤ C := by dsimp [C]; linarith
  have hc2 : C₂ ≤ C := by dsimp [C]; linarith
  have hq := mul_le_mul_of_nonneg_right hc1 (abs_nonneg q)
  have hq2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg q)
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) h0,
    mul_nonneg (sub_nonneg.mpr hq2) h0]

/-- The signed regular physical kernel has an all-time Euclidean fourth increment bound. -/
theorem u8_regular_signed_kernel_fourth_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) := by
  apply u8_regular_kernel_fourth_increment_of_ac hd ω lam Λ hΛ hω
  intro t ht x
  apply (u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht x).trans
  apply Measure.ae_le_iff_absolutelyContinuous.mp
  intro P hP
  exact (Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mp hP

/-- Centered coordinate exponential growth for the signed regular kernel. -/
theorem u8_regular_signed_coordinate_exponential_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (i : Fin d) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (a * ((y - x) i)))
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) := by
  obtain ⟨B, hB, hb⟩ := u5_regular_kernel_coordinate_exp_growth hd ω lam Λ hΛ hω i a
  refine ⟨B + 1, by linarith, ?_⟩
  intro t x
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  calc
    (∫⁻ y, ENNReal.ofReal (Real.exp (a * ((y - x) i))) ∂μ) =
        ENNReal.ofReal (Real.exp (-a * x i)) *
          ∫⁻ y, ENNReal.ofReal (Real.exp (a * y i)) ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 1
      simp only [Pi.sub_apply]
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-a * x i)) *
        (ENNReal.ofReal (Real.exp (a * x i)) *
          ENNReal.ofReal (Real.exp (B * (t : ℝ)))) :=
      mul_le_mul_right (hb t x) _
    _ = ENNReal.ofReal (Real.exp (B * (t : ℝ))) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      simp
    _ ≤ ENNReal.ofReal (Real.exp ((B + 1) * (t : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [t.coe_nonneg]

/-- Euclidean exponential increments for the signed regular physical kernel. -/
theorem u8_regular_signed_euclidean_exponential_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (Real.exp (q * euclideanNorm (y - x)))
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * Real.exp (C * (t : ℝ))) := by
  let Q : ℝ := q * d
  have hQ : 0 ≤ Q := mul_nonneg hq (Nat.cast_nonneg _)
  have hb (i : Fin d) (s : Bool) :=
    u8_regular_signed_coordinate_exponential_increment hd ω lam Λ hΛ hω i
      (if s then Q else -Q)
  choose B hB hbound using hb
  let D : ℝ := 1 + ∑ i : Fin d, (B i true + B i false)
  let C : ℝ := D + 2 * d
  have hD : 0 < D := by
    dsimp [D]
    have hs : 0 ≤ ∑ i : Fin d, (B i true + B i false) :=
      Finset.sum_nonneg fun i _ => add_nonneg (hB i true).le (hB i false).le
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hBD (i : Fin d) (s : Bool) : B i s ≤ D := by
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin d => B i true + B i false)
      (fun j _ => add_nonneg (hB j true).le (hB j false).le) (Finset.mem_univ i)
    have ht := hB i true
    have hf := hB i false
    cases s <;> simp only [D] <;> linarith
  refine ⟨C, hC, ?_⟩
  intro t x
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let F : Fin d → Bool → Vec d → ℝ≥0∞ := fun i s y =>
    ENNReal.ofReal (Real.exp ((if s then Q else -Q) * ((y - x) i)))
  have hm (i : Fin d) (s : Bool) : Measurable (F i s) :=
    (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_apply i).sub continuous_const))).measurable.ennreal_ofReal
  have hpoint (y : Vec d) : ENNReal.ofReal (Real.exp (q * euclideanNorm (y - x))) ≤
      ∑ i : Fin d, (F i true y + F i false y) := by
    obtain ⟨i, hi⟩ := c16_max_exists_coord_ge (by omega : 1 ≤ d)
      (y := y - x) (R := euclideanNorm (y - x)) le_rfl
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hnorm : q * euclideanNorm (y - x) ≤ Q * |(y - x) i| := by
      dsimp [Q]
      have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hdpos).mp hi) hq
      simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using h
    have he := (Real.exp_le_exp.mpr hnorm).trans
      (c16_max_exp_ge hQ (le_refl |(y - x) i|))
    have he' := ENNReal.ofReal_le_ofReal he
    rw [ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)] at he'
    apply he'.trans
    simpa [F] using
      (Finset.single_le_sum (f := fun j : Fin d => F j true y + F j false y)
        (fun j _ => bot_le) (Finset.mem_univ i))
  have hi (i : Fin d) (s : Bool) : (∫⁻ y, F i s y ∂μ) ≤
      ENNReal.ofReal (Real.exp (C * (t : ℝ))) := by
    apply (hbound i s t x).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (le_trans (hBD i s) (by dsimp [C]; linarith [show (0 : ℝ) ≤ d by positivity])) t.coe_nonneg
  calc
    _ ≤ ∫⁻ y, ∑ i : Fin d, (F i true y + F i false y) ∂μ := lintegral_mono hpoint
    _ = ∑ i : Fin d, ((∫⁻ y, F i true y ∂μ) + (∫⁻ y, F i false y ∂μ)) := by
      rw [lintegral_finsetSum (f := fun i y => F i true y + F i false y)
        Finset.univ (fun i _ => (hm i true).add (hm i false))]
      simp_rw [lintegral_add_left (hm _ true)]
    _ ≤ ∑ _i : Fin d, (ENNReal.ofReal (Real.exp (C * (t : ℝ))) +
        ENNReal.ofReal (Real.exp (C * (t : ℝ)))) :=
      Finset.sum_le_sum fun i _ => add_le_add (hi i true) (hi i false)
    _ = ENNReal.ofReal ((2 * d) * Real.exp (C * (t : ℝ))) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (d : ℝ))]
      congr 1 <;> ring
    _ ≤ ENNReal.ofReal (C * Real.exp (C * (t : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      dsimp [C]
      linarith

/-- Exponential Euclidean displacement tail for the signed regular kernel. -/
theorem u8_regular_signed_kernel_exponential_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d) (R : ℝ), 0 ≤ R →
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
        {y | R ≤ euclideanNorm (y - x)} ≤
      ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - q * R)) := by
  obtain ⟨C, hC, hbound⟩ :=
    u8_regular_signed_euclidean_exponential_increment hd ω lam Λ hΛ hω q hq.le
  refine ⟨C, hC, ?_⟩
  intro t x R _hR
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let f : Vec d → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (q * euclideanNorm (y - x)))
  have hf : Measurable f :=
    (Real.continuous_exp.comp (continuous_const.mul
      ((EinsteinFull.Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)))).measurable.ennreal_ofReal
  have hsub : {y : Vec d | R ≤ euclideanNorm (y - x)} ⊆
      {y | ENNReal.ofReal (Real.exp (q * R)) ≤ f y} := by
    intro y hy
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hy hq.le))
  calc
    μ {y | R ≤ euclideanNorm (y - x)} ≤
        μ {y | ENNReal.ofReal (Real.exp (q * R)) ≤ f y} := measure_mono hsub
    _ ≤ (∫⁻ y, f y ∂μ) / ENNReal.ofReal (Real.exp (q * R)) :=
      meas_ge_le_lintegral_div hf.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C * Real.exp (C * (t : ℝ))) /
        ENNReal.ofReal (Real.exp (q * R)) := by
      apply ENNReal.div_le_div_right _ _
      simpa only [f, μ] using hbound t x
    _ = ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - q * R)) := by
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      rw [Real.exp_sub]
      ring

/-- Gaussian Euclidean displacement tail for the signed regular physical kernel. -/
theorem u8_regular_signed_kernel_gaussian_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
          {y | R ≤ euclideanNorm (y - x)} ≤
        ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
  obtain ⟨B, hB, hmgf⟩ := u8_regular_signed_uniform_coordinate_mgf hd ω lam Λ hΛ hω
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  let C : ℝ := B + 2 * d + 1
  let c : ℝ := 1 / (8 * B * (d : ℝ) ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro t ht x R hR
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  let q : ℝ := R / (2 * B * d * (t : ℝ))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let F : Fin d → Bool → Vec d → ℝ≥0∞ := fun i s y =>
    ENNReal.ofReal (Real.exp ((if s then q else -q) * ((y - x) i)))
  have hm (i : Fin d) (s : Bool) : Measurable (F i s) :=
    (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_apply i).sub continuous_const))).measurable.ennreal_ofReal
  let f : Vec d → ℝ≥0∞ := fun y => ∑ i : Fin d, (F i true y + F i false y)
  have hf : Measurable f := Finset.measurable_sum _ (fun i _ => (hm i true).add (hm i false))
  have hsub : {y : Vec d | R ≤ euclideanNorm (y - x)} ⊆
      {y | ENNReal.ofReal (Real.exp (q * (R / d))) ≤ f y} := by
    intro y hy
    obtain ⟨i, hi⟩ := c16_max_exists_coord_ge (by omega : 1 ≤ d) hy
    have he := ENNReal.ofReal_le_ofReal (c16_max_exp_ge hq hi)
    rw [ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)] at he
    exact he.trans (by simpa [f, F] using
      (Finset.single_le_sum (f := fun j : Fin d => F j true y + F j false y)
        (fun j _ => bot_le) (Finset.mem_univ i)))
  have hi (i : Fin d) (s : Bool) : (∫⁻ y, F i s y ∂μ) ≤
      ENNReal.ofReal (Real.exp (B * (q + q ^ 2) * (t : ℝ))) := by
    have h := hmgf (if s then q else -q) i t x
    cases s <;> simpa [F, μ, abs_of_nonneg hq, abs_of_nonpos (neg_nonpos.mpr hq)] using h
  have hint : (∫⁻ y, f y ∂μ) ≤
      ENNReal.ofReal ((2 * d) * Real.exp (B * (q + q ^ 2) * (t : ℝ))) := by
    calc
      _ = ∑ i : Fin d, ((∫⁻ y, F i true y ∂μ) + (∫⁻ y, F i false y ∂μ)) := by
        dsimp [f]
        rw [lintegral_finsetSum (f := fun i y => F i true y + F i false y)
          Finset.univ (fun i _ => (hm i true).add (hm i false))]
        simp_rw [lintegral_add_left (hm _ true)]
      _ ≤ ∑ _i : Fin d, (ENNReal.ofReal (Real.exp (B * (q + q ^ 2) * (t : ℝ))) +
          ENNReal.ofReal (Real.exp (B * (q + q ^ 2) * (t : ℝ)))) :=
        Finset.sum_le_sum fun i _ => add_le_add (hi i true) (hi i false)
      _ = _ := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (d : ℝ))]
        congr 1 <;> ring
  have hexp : B * (q + q ^ 2) * (t : ℝ) - q * (R / d) ≤
      C * (t : ℝ) - c * R ^ 2 / (t : ℝ) := by
    have hs : 0 ≤ (R - 2 * B * (d : ℝ) * (t : ℝ)) ^ 2 := sq_nonneg _
    dsimp [q, C, c]
    field_simp
    have hp : 0 ≤ B * (d : ℝ) ^ 2 * (t : ℝ) ^ 2 * (B + 4 * d + 2) := by positivity
    nlinarith only [hs, hp]
  calc
    μ {y | R ≤ euclideanNorm (y - x)} ≤
        μ {y | ENNReal.ofReal (Real.exp (q * (R / d))) ≤ f y} := measure_mono hsub
    _ ≤ (∫⁻ y, f y ∂μ) / ENNReal.ofReal (Real.exp (q * (R / d))) :=
      meas_ge_le_lintegral_div hf.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 * d) * Real.exp (B * (q + q ^ 2) * (t : ℝ))) /
        ENNReal.ofReal (Real.exp (q * (R / d))) := ENNReal.div_le_div_right hint _
    _ = ENNReal.ofReal ((2 * d) * Real.exp
        (B * (q + q ^ 2) * (t : ℝ) - q * (R / d))) := by
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      rw [Real.exp_sub]
      ring
    _ ≤ ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul (by dsimp [C]; linarith) (Real.exp_le_exp.mpr hexp)
        (Real.exp_nonneg _) hC.le

#print axioms u8_regular_signed_kernel_gaussian_tail

#print axioms u8_regular_cutoff_product_quantitative
#print axioms u8_regular_uniform_bounded_coordinate_generator

#print axioms u8_regular_signed_kernel_exponential_tail

#print axioms u8_regular_signed_euclidean_exponential_increment

#print axioms u8_regular_signed_kernel_fourth_increment


private theorem u8_joint_of_restart {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (κ : ProbabilityTheory.Kernel A B) [ProbabilityTheory.IsMarkovKernel κ]
    (h : ∀ C : Set A, MeasurableSet C →
      (μ.restrict (X ⁻¹' C)).map Y =
        (ProbabilityTheory.Kernel.comap κ X hX) ∘ₘ (μ.restrict (X ⁻¹' C))) :
    μ.map (fun z => (X z, Y z)) = (μ.map X).compProd κ := by
  apply Measure.ext_prod
  intro C D hC hD
  have hh := congrArg (fun m : Measure B => m D) (h C hC)
  rw [Measure.map_apply hY hD, Measure.bind_apply hD (ProbabilityTheory.Kernel.aemeasurable _),
    Measure.restrict_apply (hY hD)] at hh
  simp_rw [ProbabilityTheory.Kernel.comap_apply] at hh
  rw [Measure.map_apply (hX.prodMk hY) (hC.prod hD), Set.mk_preimage_prod,
    Measure.compProd_apply_prod hC hD,
    setLIntegral_map hC (κ.measurable_coe hD) hX]
  simpa only [Set.inter_comm] using hh

/-- Every supplied regular realization inherits the signed kernel's fourth increment bound. -/
theorem u8_supplied_regular_fourth_increment
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h0 h1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : ℝ≥0), s ≤ t → ∀ x : Vec d,
      (∫⁻ γ, ENNReal.ofReal (euclideanNorm (γ t - γ s) ^ 4)
        ∂G.pathLaw x) ≤
      ENNReal.ofReal (C * (((t : ℝ) - (s : ℝ)) ^ 2 +
        ((t : ℝ) - (s : ℝ)) ^ 4)) := by
  let : ProbabilityTheory.IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let S := u2RegularC0KernelSemigroup hd ω lam L hL hω
  have hfdd := u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam L hL hω h0 h1 G
  obtain ⟨C, hC, hmoment⟩ := u8_regular_signed_kernel_fourth_increment hd ω lam L hL hω
  refine ⟨C, hC, ?_⟩
  intro s t hst x
  let X : Path d → Vec d := fun γ => γ s
  let Y : Path d → Path d := ContinuousPath.shift s
  have hX : Measurable X := ContinuousPath.measurable_coordinateProcess s
  have hY : Measurable Y := ContinuousPath.measurable_shift_fixed s
  have hjoint : (G.pathLaw x).map (fun γ => (X γ, Y γ)) =
      ((G.pathLaw x).map X).compProd G.pathLaw := by
    apply u8_joint_of_restart (G.pathLaw x) X Y hX hY G.pathLaw
    intro A hA
    apply (u2RegularC0KernelSemigroup_isFeller hd ω lam L hL hω).realization_restrict_map_shift
      S (u2_regular_kernel_conservative hd ω lam L hL hω)
      (ContinuousMap.const ℝ≥0 (0 : Vec d)) G.pathLaw hfdd x s
    exact (ContinuousPath.measurable_coordinateProcess_canonicalFiltration s) hA
  let F : Vec d × Path d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (euclideanNorm (z.2 (t - s) - z.1) ^ 4)
  have hF : Measurable F := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply EinsteinRelation.Entropy.continuous_euclideanNorm'.measurable.comp
    exact ((ContinuousPath.measurable_coordinateProcess (t - s)).comp measurable_snd).sub measurable_fst
  have hinner (y : Vec d) : ∫⁻ η, F (y, η) ∂G.pathLaw y ≤
      ENNReal.ofReal (C * ((↑(t - s) : ℝ) ^ 2 + (↑(t - s) : ℝ) ^ 4)) := by
    have hmarg := Blueprint.k11_endpoint S G.pathLaw hfdd (t - s) y
    have hm := hmoment (t - s) y
    have hf : Measurable (fun z : Vec d => ENNReal.ofReal (euclideanNorm (z - y) ^ 4)) := by
      apply Measurable.ennreal_ofReal
      apply Measurable.pow_const
      exact EinsteinRelation.Entropy.continuous_euclideanNorm'.measurable.comp
        (measurable_id.sub measurable_const)
    change (G.pathLaw y).map (ContinuousPath.coordinateProcess (t - s)) =
      (S.kernel (t - s)) y at hmarg
    rw [← hmarg, lintegral_map hf (ContinuousPath.measurable_coordinateProcess (t - s))] at hm
    exact hm
  calc
    _ = ∫⁻ z, F z ∂((G.pathLaw x).map (fun γ => (X γ, Y γ))) := by
      rw [lintegral_map hF (hX.prodMk hY)]
      congr 1
      funext γ
      simp [F, X, Y, ContinuousPath.shift, add_tsub_cancel_of_le hst]
    _ = ∫⁻ y, ∫⁻ η, F (y, η) ∂G.pathLaw y ∂((G.pathLaw x).map X) := by
      rw [hjoint, Measure.lintegral_compProd hF]
    _ ≤ _ := by
      have h := lintegral_mono (μ := (G.pathLaw x).map X) hinner
      simpa [NNReal.coe_sub hst] using h


/-- The supplied realization inherits a general continuous-path maximal inequality
from its fourth increments and its starting-point property. -/
theorem u8_supplied_regular_path_maximal_tail_of_inequality
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h0 h1)
    (hmax : ∀ (K : Kernel (Vec d) (Path d)) (B : ℝ), 0 < B →
      (∀ x : Vec d, ∀ᵐ γ ∂K x, γ 0 = x) →
      (∀ (s t : ℝ≥0), s ≤ t → ∀ x : Vec d,
        (∫⁻ γ, ENNReal.ofReal (euclideanNorm (γ t - γ s) ^ 4) ∂K x) ≤
          ENNReal.ofReal (B * (((t : ℝ) - (s : ℝ)) ^ 2 +
            ((t : ℝ) - (s : ℝ)) ^ 4))) →
      ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ≥0, 0 < T → ∀ (x : Vec d) (R : ℝ), 0 < R →
        K x {γ | ∃ t : ℝ≥0, t ≤ T ∧ R ≤ euclideanNorm (γ t - x)} ≤
          ENNReal.ofReal (C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / R ^ 4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ≥0, 0 < T → ∀ (x : Vec d) (R : ℝ), 0 < R →
      G.pathLaw x {γ | ∃ t : ℝ≥0, t ≤ T ∧ R ≤ euclideanNorm (γ t - x)} ≤
        ENNReal.ofReal (C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / R ^ 4) := by
  obtain ⟨B, hB, hinc⟩ := u8_supplied_regular_fourth_increment hd L hL ω hω lam h0 h1 G
  exact hmax G.pathLaw B hB G.pathLaw_starts_at hinc

end EinsteinFull
