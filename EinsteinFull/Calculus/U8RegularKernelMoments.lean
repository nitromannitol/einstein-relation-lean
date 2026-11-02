import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import EinsteinFull.Calculus.U2GMPHeatDensity
import EinsteinFull.Calculus.U6GMPKernelFourthMoment

open MeasureTheory Filter Set
open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
namespace EinsteinFull
open Blueprint

/-- At positive times, absolute continuity transfers the regular generator's
almost-everywhere growth estimate to each starting point. -/
theorem u8_regular_squareCutoff_generator_time_bound_of_ac
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0, 0 < t →
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam
        (gmpPhysicalCoordinateMomentCutoff x k 1 a) y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤ A + B * (t : ℝ) := by
  obtain ⟨A, B, hA, hB, hgen⟩ :=
    u2_regular_coordinateSquareCutoff_generator_ae_bound hd ω lam Λ hΛ hω
  obtain ⟨C, hC, hm⟩ := u2_regular_kernel_coordinateAbs_integrable_le hd ω lam Λ hΛ hω
  refine ⟨A + B, A * C, add_nonneg hA hB, mul_nonneg hA hC, ?_⟩
  intro x k a ha t ht
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let : IsProbabilityMeasure μ := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
  let φ := gmpPhysicalCoordinateMomentCutoff x k 1 a
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam φ
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  obtain ⟨D, _, hgD⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hp.1 hp.2.1
  have hg : Integrable g μ := Integrable.of_bound
    (measurable_physicalGenerator (firstCoordinateIndex hd) ω lam φ).aestronglyMeasurable D
    (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hgD y)
  have hm0 := (hm x k t).1
  have hh : Integrable (fun y => A * |y k - x k| + B) μ :=
    (hm0.const_mul A).add (integrable_const B)
  have hae : ∀ᵐ y ∂μ, g y ≤ A * |y k - x k| + B := by
    filter_upwards [(hac t ht x).ae_le hgen] with y hy
    exact (abs_le.mp (hy x k a ha)).2
  have h := integral_mono_ae hg hh hae
  change (∫ y, g y ∂μ) ≤ _
  calc
    _ ≤ ∫ y, (A * |y k - x k| + B) ∂μ := h
    _ = A * (∫ y, |y k - x k| ∂μ) + B := by
      rw [integral_add (hm0.const_mul A) (integrable_const B), integral_const_mul]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      rfl
    _ ≤ A + B + A * C * (t : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left (hm x k t).2 hA
      nlinarith

#print axioms u8_regular_squareCutoff_generator_time_bound_of_ac

/-- A pointwise bound on a positive-time orbit integrates over a finite horizon. -/
theorem u8_intervalIntegral_le_const_mul (F : ℝ → ℝ) (t M : ℝ)
    (ht : 0 ≤ t) (hi : IntervalIntegrable F volume 0 t)
    (hb : ∀ s ∈ Set.Ioc (0 : ℝ) t, F s ≤ M) :
    (∫ s in (0 : ℝ)..t, F s) ≤ M * t := by
  rw [intervalIntegral.integral_of_le ht]
  have hF : IntegrableOn F (Set.Ioc (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hi
  have hM : IntegrableOn (fun _ : ℝ => M) (Set.Ioc (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (intervalIntegrable_const)
  have h := integral_mono_ae hF hM (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hb s hs)
  calc
    _ ≤ ∫ _s in Set.Ioc (0 : ℝ) t, M := h
    _ = M * t := by simp [ht, mul_comm]

#print axioms u8_intervalIntegral_le_const_mul

/-- A compact test's generator orbit is integrable on every finite time interval. -/
theorem u8_regular_generator_orbit_intervalIntegrable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (x : Vec d) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) volume 0 t := by
  obtain ⟨D, hD, hm, hb⟩ := u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω φ hφ hc
  have hm' := hm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => x)))
  apply (intervalIntegrable_const (c := D)).mono_fun hm'.aestronglyMeasurable
  filter_upwards with s
  simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, Real.norm_of_nonneg hD] using
    hb (Real.toNNReal s) x

#print axioms u8_regular_generator_orbit_intervalIntegrable

/-- The positive-time cutoff generator bound integrates along each regular kernel orbit. -/
theorem u8_regular_squareCutoff_generator_integral_bound_of_ac
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      (∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam
          (gmpPhysicalCoordinateMomentCutoff x k 1 a) y ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) ≤
        (A + B * (t : ℝ)) * (t : ℝ) := by
  obtain ⟨A, B, hA, hB, hb⟩ :=
    u8_regular_squareCutoff_generator_time_bound_of_ac hd ω lam Λ hΛ hω hac
  refine ⟨A, B, hA, hB, ?_⟩
  intro x k a ha t
  let φ := gmpPhysicalCoordinateMomentCutoff x k 1 a
  let F : ℝ → ℝ := fun s => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
    u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hi : IntervalIntegrable F volume 0 t :=
    u8_regular_generator_orbit_intervalIntegrable hd ω lam Λ hΛ hω φ hp.1 hp.2.1 x t
  apply u8_intervalIntegral_le_const_mul F t (A + B * (t : ℝ)) t.coe_nonneg hi
  intro s hs
  have hpos : 0 < Real.toNNReal s := Real.toNNReal_pos.mpr hs.1
  have h := hb x k a ha (Real.toNNReal s) hpos
  have hst : (Real.toNNReal s : ℝ) ≤ (t : ℝ) := by
    rw [Real.coe_toNNReal s hs.1.le]
    exact hs.2
  have hm := mul_le_mul_of_nonneg_left hst hB
  change F s ≤ A + B * (t : ℝ)
  linarith only [h, hm]

#print axioms u8_regular_squareCutoff_generator_integral_bound_of_ac

/-- Dynkin's formula and the integrated generator bound give the cutoff estimate. -/
theorem u8_regular_squareCutoff_bound_of_ac_dynkin
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam)
    (hdyn : ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ (t : ℝ≥0) (x : Vec d),
      (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) - φ x =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      (∫ y, gmpPhysicalCoordinateMomentCutoff x k 1 a y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        (A + B * (t : ℝ)) * (t : ℝ) := by
  obtain ⟨A, B, hA, hB, hb⟩ :=
    u8_regular_squareCutoff_generator_integral_bound_of_ac hd ω lam Λ hΛ hω hac
  refine ⟨A, B, hA, hB, ?_⟩
  intro x k a ha t
  let φ := gmpPhysicalCoordinateMomentCutoff x k 1 a
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hz : φ x = 0 := by simp [φ, gmpPhysicalCoordinateMomentCutoff]
  have h := hdyn φ hp.1 hp.2.1 t x
  rw [hz, sub_zero] at h
  exact h.le.trans (hb x k a ha t)

#print axioms u8_regular_squareCutoff_bound_of_ac_dynkin

/-- A uniform square-cutoff estimate passes to the actual coordinate moment. -/
theorem u8_regular_coordinateSquare_of_cutoff_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcut : ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      (∫ y, gmpPhysicalCoordinateMomentCutoff x k 1 a y ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ)) :
    ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      Integrable (fun y => (y k - x k) ^ 2)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) := by
  intro x k t
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := P t x
  let : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let D : ℝ := (A + B * (t : ℝ)) * (t : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb (m : ℕ) :
      (∫⁻ y, ENNReal.ofReal (gmpPhysicalCoordinateMomentCutoff x k 1 (((m : ℝ) + 1)⁻¹) y) ∂μ) ≤
        ENNReal.ofReal D := by
    let a : ℝ := ((m : ℝ) + 1)⁻¹
    have ha : 0 < a := by dsimp [a]; positivity
    have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
    have hi : Integrable (gmpPhysicalCoordinateMomentCutoff x k 1 a) μ :=
      hp.1.continuous.integrable_of_hasCompactSupport hp.2.1
    change (∫⁻ y, ENNReal.ofReal (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun y => (hp.2.2.1 y).1))]
    exact ENNReal.ofReal_le_ofReal (hcut x k a ha t)
  have hl : (∫⁻ y, ENNReal.ofReal ((y k - x k) ^ 2) ∂μ) ≤ ENNReal.ofReal D := by
    have h := (gmpPhysical_coordinateMomentCutoff_fatou x k 1 μ).trans
      (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hb))
    simpa using h
  have hc : Continuous (fun y : Vec d => (y k - x k) ^ 2) := by fun_prop
  have h0 : ∀ y : Vec d, 0 ≤ (y k - x k) ^ 2 := fun y => sq_nonneg _
  have hint : Integrable (fun y => (y k - x k) ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable (ae_of_all _ h0)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff hD).1 hl


/-- Coordinate moment estimates combine into the Euclidean increment estimate. -/
theorem u8_regular_increment_of_coordinateSquare_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcoord : ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      Integrable (fun y => (y k - x k) ^ 2)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 2)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * ((t : ℝ) + (t : ℝ) ^ 2)) := by
  refine ⟨(d : ℝ) * (A + B) + 1, by positivity, ?_⟩
  intro t x
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  have hsq (y : Vec d) : euclideanNorm (y - x) ^ 2 = ∑ k : Fin d, (y k - x k) ^ 2 := by
    unfold euclideanNorm euclideanSq dot
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg ((y - x) i)))]
    simp only [Pi.sub_apply, pow_two]
  have hint : Integrable (fun y : Vec d => euclideanNorm (y - x) ^ 2) μ := by
    simp_rw [hsq]
    exact integrable_finsetSum _ fun k _ => (hcoord x k t).1
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun y => sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [hsq]
  rw [integral_finsetSum _ (fun k _ => (hcoord x k t).1)]
  have hs : (∑ k : Fin d, ∫ y, (y k - x k) ^ 2 ∂μ) ≤
      (d : ℝ) * ((A + B * (t : ℝ)) * (t : ℝ)) := by
    calc
      _ ≤ ∑ _k : Fin d, ((A + B * (t : ℝ)) * (t : ℝ)) :=
        Finset.sum_le_sum fun k _ => (hcoord x k t).2
      _ = _ := by simp
  have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hd0 hA, mul_nonneg hd0 hB,
    mul_nonneg (mul_nonneg hd0 hA) (sq_nonneg (t : ℝ)),
    mul_nonneg (mul_nonneg hd0 hB) ht, sq_nonneg (t : ℝ)]

/-- Translation of a bounded measurable orbit on nonnegative times. -/
theorem u8_nnreal_orbit_primitive_shift (G : ℝ≥0 → ℝ)
    (hm : Measurable (fun s : ℝ => G (Real.toNNReal s)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ s, ‖G s‖ ≤ B) (r t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), G (r + Real.toNNReal s)) =
      (∫ s in (0 : ℝ)..((r : ℝ) + t), G (Real.toNNReal s)) -
      ∫ s in (0 : ℝ)..(r : ℝ), G (Real.toNNReal s) := by
  let H : ℝ → ℝ := fun s => G (Real.toNNReal s)
  have ht : (∫ s in (0 : ℝ)..(t : ℝ), G (r + Real.toNNReal s)) =
      ∫ s in (0 : ℝ)..(t : ℝ), H (s + r) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (Set.uIcc_of_le t.coe_nonneg ▸ hs).1
    have heq : r + Real.toNNReal s = Real.toNNReal (s + r) := by
      apply NNReal.eq
      simp only [NNReal.coe_add, Real.coe_toNNReal _ hs0,
        Real.coe_toNNReal _ (add_nonneg hs0 r.coe_nonneg)]
      exact add_comm _ _
    exact congrArg G heq
  rw [ht]
  exact u2_bounded_orbit_primitive_shift H hm B hB (fun s => hb (Real.toNNReal s)) r t

/-- Translation of the integral orbit of an arbitrary kernel and observable. -/
theorem u8_kernel_orbit_shift {α : Type*} [MeasurableSpace α]
    (P : ℝ≥0 → Measure α) (g : α → ℝ)
    (hm : Measurable (fun s : ℝ => ∫ y, g y ∂P (Real.toNNReal s)))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ q : ℝ≥0, ‖∫ y, g y ∂P q‖ ≤ B)
    (r t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), ∫ y, g y ∂P (r + Real.toNNReal s)) =
    (∫ s in (0 : ℝ)..((r : ℝ) + t), ∫ y, g y ∂P (Real.toNNReal s)) -
    (∫ s in (0 : ℝ)..(r : ℝ), ∫ y, g y ∂P (Real.toNNReal s)) := by
  exact u8_nnreal_orbit_primitive_shift (fun q => ∫ y, g y ∂P q) hm B hB hb r t

/-- Positive-time kernel absolute continuity extends the almost-everywhere
compact-test Dynkin identity to every starting point. -/
theorem u8_regular_compactTest_dynkin_of_ac {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (t : ℝ≥0) (x : Vec d) :
    (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) - φ x =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x := by
  let f := gmpPhysicalCompactC0 φ hφ.continuous hc
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f g; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  let F : ℝ → ℝ := fun r => ev (S (Real.toNNReal r) f)
  let G : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, ∫ y,
    physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x
  have hF : Continuous F := ev.continuous.comp (S.continuous_operator_toNNReal f)
  have hG : Continuous G := u2_regular_generator_orbit_primitive_continuous hd ω lam Λ hΛ hω φ hφ hc x
  have hshift (r : ℝ) (hr : 0 < r) : F (r + t) - F r = G (r + t) - G r := by
    have hh := u2_regular_kernel_compactTest_dynkin_shifted hd ω lam Λ hΛ hω φ hφ hc
      (Real.toNNReal r) t x (hac (Real.toNNReal r) (Real.toNNReal_pos.mpr hr) x)
    obtain ⟨B, hB, hm, hb⟩ :=
      u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω φ hφ hc
    have hm' := hm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => x)))
    have hb' (q : ℝ≥0) : ‖∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω q x‖ ≤ B := by
      simpa only [Real.norm_eq_abs] using hb q x
    have hJ := u8_kernel_orbit_shift (fun q => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω q x)
      (physicalGenerator (firstCoordinateIndex hd) ω lam φ) hm' B hB hb' (Real.toNNReal r) t
    rw [hJ] at hh
    have hrt : Real.toNNReal (r + (t : ℝ)) = Real.toNNReal r + t := by
      apply NNReal.eq
      simp [hr.le]
    have heq (q : ℝ≥0) : (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω q x) = ev (S q f) :=
      u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω q f x
    rw [heq, heq] at hh
    simpa only [F, G, hrt, Real.coe_toNNReal _ hr.le, NNReal.coe_add] using hh
  have hclosed : IsClosed {r : ℝ | F (r + t) - F r = G (r + t) - G r} :=
    isClosed_eq ((hF.comp (continuous_id.add continuous_const)).sub hF)
      ((hG.comp (continuous_id.add continuous_const)).sub hG)
  have hzero : (0 : ℝ) ∈ {r : ℝ | F (r + t) - F r = G (r + t) - G r} := by
    apply closure_minimal (s := Set.Ioi (0 : ℝ)) (fun r hr => hshift r hr) hclosed
    rw [closure_Ioi]
    exact (le_rfl : (0 : ℝ) ≤ 0)
  have hkernel (q : ℝ≥0) : (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω q x) = ev (S q f) :=
    u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω q f x
  have hz : (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω 0 x) = φ x := by
    simp [ProbabilityTheory.Kernel.id_apply]
  simpa only [Set.mem_ofPred_eq, zero_add, F, G, Real.toNNReal_coe,
    Real.toNNReal_zero, intervalIntegral.integral_same, sub_zero, ← hkernel, hz] using hzero

#print axioms u8_regular_compactTest_dynkin_of_ac

/-- The regular second-increment estimate follows from every-start absolute
continuity and the compact-test Dynkin identity for the same kernel. -/
theorem u8_regular_kernel_second_increment_of_ac_dynkin
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam)
    (hdyn : ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ (t : ℝ≥0) (x : Vec d),
      (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) - φ x =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 2)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * ((t : ℝ) + (t : ℝ) ^ 2)) := by
  obtain ⟨A, B, hA, hB, hcut⟩ :=
    u8_regular_squareCutoff_bound_of_ac_dynkin hd ω lam Λ hΛ hω hac hdyn
  apply u8_regular_increment_of_coordinateSquare_bound hd ω lam Λ hΛ hω A B hA hB
  exact u8_regular_coordinateSquare_of_cutoff_bound hd ω lam Λ hΛ hω A B hA hB hcut

/-- Every-start absolute continuity gives the regular kernel second increment. -/
theorem u8_regular_kernel_second_increment_of_ac
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 2)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * ((t : ℝ) + (t : ℝ) ^ 2)) := by
  exact u8_regular_kernel_second_increment_of_ac_dynkin hd ω lam Λ hΛ hω hac
    (u8_regular_compactTest_dynkin_of_ac hd ω lam Λ hΛ hω hac)

/-- At zero force the regular kernel satisfies the unconditional Euclidean
second-increment estimate at every starting point. -/
theorem u8_regular_unforced_kernel_second_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 2)
        ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * ((t : ℝ) + (t : ℝ) ^ 2)) := by
  apply u8_regular_kernel_second_increment_of_ac hd ω 0 Λ hΛ hω
  intro t ht x
  obtain ⟨M, _, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  have hv : u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := Measure.absolutelyContinuous_of_le_smul (hdom x)
  have hm : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd 0 :=
    Measure.absolutelyContinuous_of_le_smul
      (u4_unforced_physical_measure_comparable hd ω Λ hω).2
  exact hv.trans hm

#print axioms u8_regular_unforced_kernel_second_increment

#print axioms u8_regular_kernel_second_increment_of_ac

#print axioms u8_regular_kernel_second_increment_of_ac_dynkin

#print axioms u8_regular_increment_of_coordinateSquare_bound

#print axioms u8_regular_coordinateSquare_of_cutoff_bound

/-- A uniform local fourth moment for the regular kernel propagates to all times. -/
theorem u8_regular_kernel_fourth_increment_of_local
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hlocal : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        ENNReal.ofReal (C * (t : ℝ) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) := by
  obtain ⟨C, δ, hC, hδ, hm⟩ := hlocal
  refine ⟨C * (2 * (1 + δ⁻¹ ^ 2)), by positivity, ?_⟩
  intro t x
  obtain ⟨n, hn, hstep, hcount⟩ := u6_equal_time_steps (t : ℝ) δ t.property hδ
  let u : ℝ≥0 := t / (n : ℝ≥0)
  have hnNN : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hu : (u : ℝ) = (t : ℝ) / (n : ℝ) := by simp [u]
  have ht : n • u = t := by
    rw [nsmul_eq_mul]
    change (n : ℝ≥0) * (t / (n : ℝ≥0)) = t
    rw [mul_comm, div_mul_cancel₀ _ hnNN]
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  letI : ProbabilityTheory.IsMarkovKernel (P u) := ⟨fun z =>
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω u z⟩⟩
  have hstepBound : ∀ z, (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - z) ^ 4) ∂P u z) ≤
      ENNReal.ofReal (C * (u : ℝ) ^ 2) := by
    intro z
    exact hm z u (by simpa [hu] using hstep)
  have hsem := u6_semigroup_fourth_moment_steps P u x n
    (ENNReal.ofReal (C * (u : ℝ) ^ 2)) hstepBound
  rw [ht] at hsem
  have hprod : (n : ℝ) ^ 3 * ((n : ℝ) * (C * (u : ℝ) ^ 2)) =
      C * ((n : ℝ) ^ 2 * (t : ℝ) ^ 2) := by
    rw [hu]
    field_simp
  have hcast : (n : ℝ≥0∞) ^ 3 * ((n : ℝ≥0∞) * ENNReal.ofReal (C * (u : ℝ) ^ 2)) =
      ENNReal.ofReal (C * ((n : ℝ) ^ 2 * (t : ℝ) ^ 2)) := by
    rw [← hprod, ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ) ^ 3),
      ENNReal.ofReal_mul hn0, ENNReal.ofReal_pow hn0, ENNReal.ofReal_natCast]
  have hb := mul_le_mul_of_nonneg_left
    (u6_step_count_growth_bound (t : ℝ) δ n t.property hδ hcount) hC.le
  calc
    _ ≤ (n : ℝ≥0∞) ^ 3 * ((n : ℝ≥0∞) * ENNReal.ofReal (C * (u : ℝ) ^ 2)) := hsem
    _ = ENNReal.ofReal (C * ((n : ℝ) ^ 2 * (t : ℝ) ^ 2)) := hcast
    _ ≤ ENNReal.ofReal ((C * (2 * (1 + δ⁻¹ ^ 2))) *
        ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) := ENNReal.ofReal_le_ofReal (by nlinarith [hb])

#print axioms u8_regular_kernel_fourth_increment_of_local

/-! Local fourth-moment bootstrap adapted from U6RegularPathRealization. -/

/-- The regular fourth-cutoff generator obeys a common almost-everywhere growth bound. -/
theorem u8_local_regular_squaredSquareCutoff_generator_ae_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, ∀ (z : Vec d) (k : Fin d) (a : ℝ), 0 < a →
      let f := gmpPhysicalCoordinateMomentCutoff z k 1 a
      |physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => (f y) ^ 2) x| ≤
        A * (x k - z k) ^ 2 + B * (f x) ^ 2 := by
  obtain ⟨D, hD, hderiv⟩ := gmpPhysical_squaredSquareCutoff_derivative_bounds (d := d)
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨C₁ * D + C₂ * (2 * D + 2 * D ^ 2), C₁ * D, by positivity, by positivity, ?_⟩
  filter_upwards [(gmpPhysical_ae_iff_volume hd ω lam _).mpr hg] with x hx
  intro z k a ha
  let f := gmpPhysicalCoordinateMomentCutoff z k 1 a
  let q : ℝ := x k - z k
  have hs : ContDiff ℝ 2 (fun y => (f y) ^ 2) :=
    ((gmpPhysical_coordinateMomentCutoff_properties z k 1 a ha).1.pow 2).of_le (by simp)
  have hfirst (i : Fin d) :
      |fderiv ℝ (fun y => (f y) ^ 2) x (unitVector i)| ≤ D * (q ^ 2 + (f x) ^ 2) := by
    have h := (hderiv z x k i i a ha).1
    have hq : |q| ^ 2 = q ^ 2 := sq_abs q
    nlinarith [sq_nonneg (|q| - f x), mul_nonneg hD (sq_nonneg (|q| - f x))]
  have hsecond (i j : Fin d) :
      |fderiv ℝ (fun y => fderiv ℝ (fun v => (f v) ^ 2) y (unitVector j)) x (unitVector i)| ≤
        (2 * D + 2 * D ^ 2) * q ^ 2 := (hderiv z x k i j a ha).2
  have h := hx _ hs (D * (q ^ 2 + (f x) ^ 2)) ((2 * D + 2 * D ^ 2) * q ^ 2)
    (by positivity) (by positivity) hfirst hsecond
  convert h using 1
  dsimp [q]
  ring

/-- Positive-time absolute continuity and square-moment integrability transfer the
fourth-cutoff generator bound to every starting point. -/
theorem u8_local_regular_squaredSquareCutoff_generator_integral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam)
    (hsecond : ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0), 0 < t →
      Integrable (fun y => (y k - x k) ^ 2)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0, 0 < t →
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam (fun v => (f v) ^ 2) y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      A * (∫ y, (y k - x k) ^ 2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) +
      B * (∫ y, (f y) ^ 2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) := by
  obtain ⟨A, B, hA, hB, hgen⟩ :=
    u8_local_regular_squaredSquareCutoff_generator_ae_bound hd ω lam Λ hΛ hω
  refine ⟨A, B, hA, hB, ?_⟩
  intro x k a ha t ht
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := P t x
  let : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hfs : ContDiff ℝ (⊤ : ℕ∞) (fun y => (f y) ^ 2) := hp.1.pow 2
  have hfc : HasCompactSupport (fun y => (f y) ^ 2) := by
    have hh : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [pow_two] using hh
  have hf : Integrable (fun y => (f y) ^ 2) μ :=
    hfs.continuous.integrable_of_hasCompactSupport hfc
  obtain ⟨D, _, hgD⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hfs hfc
  have hg : Integrable (physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => (f y) ^ 2)) μ :=
    Integrable.of_bound
      (measurable_physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => (f y) ^ 2)).aestronglyMeasurable D
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hgD y)
  have hq := hsecond x k t ht
  have hh : Integrable (fun y => A * (y k - x k) ^ 2 + B * (f y) ^ 2) μ :=
    (hq.const_mul A).add (hf.const_mul B)
  have hae : ∀ᵐ y ∂μ, physicalGenerator (firstCoordinateIndex hd) ω lam (fun v => (f v) ^ 2) y ≤
      A * (y k - x k) ^ 2 + B * (f y) ^ 2 := by
    filter_upwards [(hac t ht x).ae_le hgen] with y hy
    exact (abs_le.mp (hy x k a ha)).2
  have h := integral_mono_ae hg hh hae
  rw [integral_add (hq.const_mul A) (hf.const_mul B), integral_const_mul, integral_const_mul] at h
  exact h

/-- A fourth-cutoff integral inequality yields the local quadratic estimate. -/
theorem u8_local_regular_squaredSquareCutoff_local_of_integral_inequality
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hineq0 : ∃ A B D : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ D ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) ^ 2 + D * ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x)) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a →
      ∀ t : ℝ≥0, (t : ℝ) ≤ δ →
      (∫ y, (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2 := by
  obtain ⟨A, B, D, hA, hB, hD, hineq⟩ :=
    hineq0
  refine ⟨2 * (A + B), (2 * (D + 1))⁻¹, by positivity, by positivity, ?_⟩
  intro x k a ha t ht
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  let φ : Vec d → ℝ := fun y => (f y) ^ 2
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hs : ContDiff ℝ (⊤ : ℕ∞) φ := hp.1.pow 2
  have hcompact : HasCompactSupport φ := by
    have h : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [φ, pow_two] using h
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let F := gmpPhysicalCompactC0 φ hs.continuous hcompact
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun g => g x
        map_add' := by intro g h; rfl
        map_smul' := by intro c g; rfl } 1 (by
          intro g
          simpa using BoundedContinuousFunction.norm_coe_le_norm g.toBCF x)
  let m : ℝ → ℝ := fun s => ∫ y, φ y ∂
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x)
  have hc : Continuous m := by
    have heq (s : ℝ) : m s = ev (S (Real.toNNReal s) F) :=
      u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω (Real.toNNReal s) F x
    rw [funext heq]
    exact ev.continuous.comp (S.continuous_operator_toNNReal F)
  have hnonneg (s : ℝ) (_ : 0 ≤ s) : 0 ≤ m s := by
    apply integral_nonneg
    intro y
    exact sq_nonneg _
  have hi (s : ℝ) (hs0 : 0 ≤ s) :
      m s ≤ (A + B * s) * s ^ 2 + D * ∫ r in (0 : ℝ)..s, m r := by
    have h := hineq x k a ha (Real.toNNReal s)
    rw [Real.coe_toNNReal' s, max_eq_left hs0] at h
    exact h
  have h := gmpPhysical_quadratic_bound_of_integral_inequality m hc A B D hA hB hD hnonneg hi t t.coe_nonneg ht
  simpa [m, φ, f] using h


/-- Uniform local fourth-cutoff estimates pass to the actual coordinate moment. -/
theorem u8_local_regular_coordinateFourth_of_cutoff_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcutoff : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0, (t : ℝ) ≤ δ →
      (∫ y, (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hcut⟩ :=
    hcutoff
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro x k t ht
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := P t x
  let : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let D : ℝ := C * (t : ℝ) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb (m : ℕ) :
      (∫⁻ y, ENNReal.ofReal ((gmpPhysicalCoordinateMomentCutoff x k 1 (((m : ℝ) + 1)⁻¹) y) ^ 2) ∂μ) ≤
        ENNReal.ofReal D := by
    let a : ℝ := ((m : ℝ) + 1)⁻¹
    have ha : 0 < a := by dsimp [a]; positivity
    have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
    have hc : HasCompactSupport (fun y => (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) := by
      have hh : HasCompactSupport (fun y => gmpPhysicalCoordinateMomentCutoff x k 1 a y *
          gmpPhysicalCoordinateMomentCutoff x k 1 a y) := hp.2.1.mul_right
      simpa only [pow_two] using hh
    have hi : Integrable (fun y => (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) μ :=
      (hp.1.pow 2).continuous.integrable_of_hasCompactSupport hc
    change (∫⁻ y, ENNReal.ofReal ((gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun y => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hcut x k a ha t ht)
  have hl : (∫⁻ y, ENNReal.ofReal ((y k - x k) ^ 4) ∂μ) ≤ ENNReal.ofReal D := by
    exact (gmpPhysical_squaredSquareCutoff_fatou x k μ).trans
      (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hb))
  have hc : Continuous (fun y : Vec d => (y k - x k) ^ 4) := by fun_prop
  have h0 : ∀ y : Vec d, 0 ≤ (y k - x k) ^ 4 := fun y => by positivity
  have hint : Integrable (fun y => (y k - x k) ^ 4) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable (ae_of_all _ h0)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff hD).1 hl


/-- A regular compact-test generator orbit is time-integrable on finite intervals. -/
theorem u8_local_regular_generator_orbit_intervalIntegrable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (x : Vec d) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) volume 0 t := by
  obtain ⟨D, hD, hm, hb⟩ := u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω φ hφ hc
  have hm' := hm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => x)))
  change Measurable (fun s : ℝ => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
    u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) at hm'
  apply (intervalIntegrable_const (c := D)).mono_fun hm'.aestronglyMeasurable
  filter_upwards with s
  simpa only [Real.norm_eq_abs, Real.norm_of_nonneg hD] using hb (Real.toNNReal s) x

/-- Positive-time comparisons integrate on a finite interval. -/
theorem u8_local_intervalIntegral_mono_Ioc (F G : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hF : IntervalIntegrable F volume 0 t) (hG : IntervalIntegrable G volume 0 t)
    (h : ∀ s ∈ Set.Ioc (0 : ℝ) t, F s ≤ G s) :
    (∫ s in (0 : ℝ)..t, F s) ≤ ∫ s in (0 : ℝ)..t, G s := by
  rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
  apply integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hF)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hG)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact h s hs

/-- Dynkin's identity, every-start absolute continuity, and square moments give
 the fourth-cutoff integral inequality for the regular kernel. -/
theorem u8_local_regular_squaredSquareCutoff_integral_inequality_of_dynkin
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ physicalReversibleMeasure ω hd lam)
    (hsecond : ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      Integrable (fun y => (y k - x k) ^ 2) (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        (D + E * (t : ℝ)) * (t : ℝ))
    (hdyn : ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ (t : ℝ≥0) (x : Vec d),
      (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) - φ x =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) :
    ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) ^ 2 + C * ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ y, (f y) ^ 2 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) := by
  obtain ⟨D, E, hD, hE, hmoment⟩ := hsecond
  have hsi : ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0), 0 < t →
      Integrable (fun y => (y k - x k) ^ 2) (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) :=
    fun x k t _ => (hmoment x k t).1
  obtain ⟨A, B, hA, hB, hgen⟩ :=
    u8_local_regular_squaredSquareCutoff_generator_integral_le hd ω lam Λ hΛ hω hac hsi
  refine ⟨A * D, A * E, B, by positivity, by positivity, hB, ?_⟩
  intro x k a ha t
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  let φ : Vec d → ℝ := fun y => (f y) ^ 2
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hs : ContDiff ℝ (⊤ : ℕ∞) φ := hp.1.pow 2
  have hcompact : HasCompactSupport φ := by
    have h : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [φ, pow_two] using h
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun g => g x
        map_add' := by intro g h; rfl
        map_smul' := by intro c g; rfl } 1 (by
          intro g
          simpa using BoundedContinuousFunction.norm_coe_le_norm g.toBCF x)
  let F := gmpPhysicalCompactC0 φ hs.continuous hcompact
  have hcF : Continuous (fun s : ℝ => ∫ y, φ y ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) := by
    have heq (s : ℝ) : (∫ y, φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) =
          ev (S (Real.toNNReal s) F) :=
      u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω (Real.toNNReal s) F x
    simp_rw [heq]
    exact ev.continuous.comp (S.continuous_operator_toNNReal F)
  have hiG := u8_local_regular_generator_orbit_intervalIntegrable hd ω lam Λ hΛ hω φ hs hcompact x t
  have hpoint (s : ℝ) (hsi : s ∈ Set.Ioc 0 (t : ℝ)) :
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) ≤
      A * ((D + E * (t : ℝ)) * (t : ℝ)) + B * (∫ y, φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) := by
    have htpos : 0 < Real.toNNReal s := Real.toNNReal_pos.mpr hsi.1
    have h := hgen x k a ha (Real.toNNReal s) htpos
    have hm := (hmoment x k (Real.toNNReal s)).2
    rw [Real.coe_toNNReal' s, max_eq_left hsi.1.le] at hm
    have hpoly : (D + E * s) * s ≤ (D + E * (t : ℝ)) * (t : ℝ) := by
      nlinarith [mul_nonneg hE hsi.1.le, mul_nonneg hE t.coe_nonneg,
        mul_nonneg (sub_nonneg.mpr hsi.2) hD,
        mul_nonneg (sub_nonneg.mpr hsi.2) (mul_nonneg hE (add_nonneg hsi.1.le t.coe_nonneg))]
    have hh := mul_le_mul_of_nonneg_left (hm.trans hpoly) hA
    dsimp [φ, f] at h ⊢
    linarith
  have hi := u8_local_intervalIntegral_mono_Ioc _ _ t t.coe_nonneg hiG
    (intervalIntegrable_const.add ((hcF.intervalIntegrable 0 t).const_mul B)) hpoint
  have he := hdyn φ hs hcompact t x
  have hz : φ x = 0 := by simp [φ, f, gmpPhysicalCoordinateMomentCutoff]
  rw [hz, sub_zero] at he
  change (∫ y, φ y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ _
  rw [he]
  rw [intervalIntegral.integral_add intervalIntegrable_const ((hcF.intervalIntegrable 0 t).const_mul B),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul, sub_zero] at hi
  nlinarith [hi]


theorem u8_local_regular_euclideanFourth_of_coordinate_local
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcoord : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ δ →
      Integrable (fun y => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (∑ k : Fin d, (y k - x k) ^ 2) ^ 2 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    hcoord
  refine ⟨(d : ℝ) ^ 2 * C, δ, by positivity, hδ, ?_⟩
  intro x t ht
  let μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  have hi (k : Fin d) : Integrable (fun y => (y k - x k) ^ 4) μ := (hm x k t ht).1
  have hsum : Integrable (fun y => ∑ k : Fin d, (y k - x k) ^ 4) μ :=
    integrable_finsetSum _ (fun k _ => hi k)
  have hcont : Continuous (fun y : Vec d => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2) := by fun_prop
  have hdom : Integrable (fun y => (d : ℝ) * ∑ k : Fin d, (y k - x k) ^ 4) μ :=
    hsum.const_mul (d : ℝ)
  have htarget : Integrable (fun y => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2) μ :=
    hdom.mono_nonneg hcont.aestronglyMeasurable (ae_of_all _ (fun y => sq_nonneg _))
      (ae_of_all _ (gmpPhysical_sum_coordinateSquares_sq_le x))
  refine ⟨htarget, ?_⟩
  have h := integral_mono htarget hdom (gmpPhysical_sum_coordinateSquares_sq_le x)
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)] at h
  have hsumle : (∑ k : Fin d, ∫ y, (y k - x k) ^ 4 ∂μ) ≤
      (d : ℝ) * (C * (t : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ _k : Fin d, C * (t : ℝ) ^ 2 := Finset.sum_le_sum (fun k _ => (hm x k t ht).2)
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left hsumle (show (0 : ℝ) ≤ d by positivity)
  nlinarith [h, hh]


/-- Translate the coordinate bound to the explicit Euclidean norm. -/
theorem u8_local_regular_euclideanNormFourth_of_coordinate_local
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hcoord : ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        C * (t : ℝ) ^ 2) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ δ →
      Integrable (fun y => euclideanNorm (y - x) ^ 4)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, euclideanNorm (y - x) ^ 4 ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) ^ 2 := by
  have heq (x y : Vec d) : euclideanNorm (y - x) ^ 4 =
      (∑ k : Fin d, (y k - x k) ^ 2) ^ 2 := by
    have hs : euclideanNorm (y - x) ^ 2 = ∑ k : Fin d, (y k - x k) ^ 2 := by
      unfold euclideanNorm euclideanSq dot
      rw [Real.sq_sqrt]
      · simp only [Pi.sub_apply, pow_two]
      · exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs]
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    u8_local_regular_euclideanFourth_of_coordinate_local hd ω lam Λ hΛ hω hcoord
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro x t ht
  simpa only [heq] using hm x t ht



/-- Positive-time absolute continuity yields a local Euclidean fourth moment. -/
theorem u8_regular_kernel_fourth_local_of_ac
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ δ →
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        ENNReal.ofReal (C * (t : ℝ) ^ 2) := by
  have hdyn := u8_regular_compactTest_dynkin_of_ac hd ω lam Λ hΛ hω hac
  obtain ⟨A, B, hA, hB, hcut⟩ :=
    u8_regular_squareCutoff_bound_of_ac_dynkin hd ω lam Λ hΛ hω hac hdyn
  have hsecond := u8_regular_coordinateSquare_of_cutoff_bound hd ω lam Λ hΛ hω A B hA hB hcut
  have hineq := u8_local_regular_squaredSquareCutoff_integral_inequality_of_dynkin
    hd ω lam Λ hΛ hω hac ⟨A, B, hA, hB, hsecond⟩ hdyn
  have hcut4 := u8_local_regular_squaredSquareCutoff_local_of_integral_inequality
    hd ω lam Λ hΛ hω hineq
  have hcoord := u8_local_regular_coordinateFourth_of_cutoff_bound hd ω lam Λ hΛ hω hcut4
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    u8_local_regular_euclideanNormFourth_of_coordinate_local hd ω lam Λ hΛ hω hcoord
  refine ⟨C + 1, δ, by linarith, hδ, ?_⟩
  intro x t ht
  rw [← ofReal_integral_eq_lintegral_ofReal (hm x t ht).1
    (ae_of_all _ (fun y => by positivity))]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [(hm x t ht).2, sq_nonneg (t : ℝ)]

/-- Positive-time absolute continuity yields the all-time fourth increment. -/
theorem u8_regular_kernel_fourth_increment_of_ac
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) := by
  exact u8_regular_kernel_fourth_increment_of_local hd ω lam Λ hΛ hω
    (u8_regular_kernel_fourth_local_of_ac hd ω lam Λ hΛ hω hac)

/-- The unforced regular kernel has the all-time Euclidean fourth increment. -/
theorem u8_regular_unforced_kernel_fourth_increment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4)
        ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤
      ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) := by
  apply u8_regular_kernel_fourth_increment_of_ac hd ω 0 Λ hΛ hω
  intro t ht x
  obtain ⟨M, _, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  exact (Measure.absolutelyContinuous_of_le_smul (hdom x)).trans
    (Measure.absolutelyContinuous_of_le_smul
      (u4_unforced_physical_measure_comparable hd ω Λ hω).2)

#print axioms u8_regular_unforced_kernel_fourth_increment
#print axioms u8_regular_kernel_fourth_increment_of_ac

end EinsteinFull
