import EinsteinFull.Calculus.C5DirectionalMeanSublinearity

open EinsteinRelation MeasureTheory Filter
open Environment.AKMTestIntegralSupport ReductionImageV3
open EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.External.GilbargTrudinger
open scoped Topology BigOperators

noncomputable section
namespace EinsteinFull

/-- The increment estimate controls the mean square at a nearby point. -/
theorem c5_corrector_mean_square_nearby
    {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (physicalReferenceLaw Q))
    (C : ℝ) (hi : ∀ x y : Vec d,
      Integrable (fun ω : PhysicalField d L => euclideanNorm (χ ω x - χ ω y)^2)
        (physicalReferenceLaw Q) ∧
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x - χ ω y)^2
        ∂physicalReferenceLaw Q) ≤ C * euclideanNorm (x-y)^2)
    (x y : Vec d) :
    (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2 ∂physicalReferenceLaw Q) ≤
      2 * (∫ ω : PhysicalField d L, euclideanNorm (χ ω y)^2 ∂physicalReferenceLaw Q) +
        2 * C * euclideanNorm (x-y)^2 := by
  have hx : Integrable (fun ω : PhysicalField d L => euclideanNorm (χ ω x)^2)
      (physicalReferenceLaw Q) := by
    simpa only [Real.norm_eq_abs, sq_abs] using (hmem x).integrable_norm_pow (by decide : 2 ≠ 0)
  have hy : Integrable (fun ω : PhysicalField d L => euclideanNorm (χ ω y)^2)
      (physicalReferenceLaw Q) := by
    simpa only [Real.norm_eq_abs, sq_abs] using (hmem y).integrable_norm_pow (by decide : 2 ≠ 0)
  have hd := (hi x y).1
  have he : (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2 ∂physicalReferenceLaw Q) ≤
      2 * (∫ ω : PhysicalField d L, euclideanNorm (χ ω y)^2 ∂physicalReferenceLaw Q) +
      2 * (∫ ω : PhysicalField d L, euclideanNorm (χ ω x - χ ω y)^2 ∂physicalReferenceLaw Q) := by
    calc
      _ ≤ ∫ ω : PhysicalField d L, (2 * euclideanNorm (χ ω y)^2 +
          2 * euclideanNorm (χ ω x - χ ω y)^2) ∂physicalReferenceLaw Q := by
        apply integral_mono_ae hx ((hy.const_mul 2).add (hd.const_mul 2))
        filter_upwards with ω
        dsimp only [Pi.add_apply]
        have ht := TimeChange.euclideanNorm_add_le (χ ω y) (χ ω x - χ ω y)
        have hsum : χ ω y + (χ ω x - χ ω y) = χ ω x := by abel
        rw [hsum] at ht
        have hx0 : 0 ≤ euclideanNorm (χ ω x) := Real.sqrt_nonneg _
        have hy0 : 0 ≤ euclideanNorm (χ ω y) := Real.sqrt_nonneg _
        have hd0 : 0 ≤ euclideanNorm (χ ω x - χ ω y) := Real.sqrt_nonneg _
        nlinarith [sq_nonneg (euclideanNorm (χ ω y) - euclideanNorm (χ ω x - χ ω y))]
      _ = _ := by rw [integral_add (hy.const_mul 2) (hd.const_mul 2), integral_const_mul, integral_const_mul]
  nlinarith [(hi x y).2]

/-- A finite Euclidean net covers the unit ball. -/
theorem c5_euclidean_unit_ball_finite_net {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset (Vec d), ∀ x : Vec d, euclideanNorm x ≤ 1 →
      ∃ y ∈ s, euclideanNorm (x-y) < δ := by
  classical
  let D : ℝ := (d : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have he : 0 < δ / D := div_pos hδ hD
  have hk : IsCompact (Metric.closedBall (0 : Vec d) 1) := isCompact_closedBall 0 1
  obtain ⟨s, hs, hfin, hcover⟩ := hk.finite_cover_balls he
  refine ⟨hfin.toFinset, ?_⟩
  intro x hx
  have hnorm : ‖x‖ ≤ euclideanNorm x := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    rw [Real.norm_eq_abs]
    exact Regeneration.coordinate_abs_le_euclideanNorm x i
  have hxb : x ∈ Metric.closedBall (0 : Vec d) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm.trans hx
  have hxc := hcover hxb
  simp only [Set.mem_iUnion] at hxc
  obtain ⟨y, hy, hxy⟩ := hxc
  refine ⟨y, hfin.mem_toFinset.mpr hy, ?_⟩
  have hxy' : ‖x-y‖ < δ / D := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  calc
    euclideanNorm (x-y) ≤ D * ‖x-y‖ := euclideanNorm_le_dimension_mul_norm _
    _ < D * (δ / D) := mul_lt_mul_of_pos_left hxy' hD
    _ = δ := mul_div_cancel₀ δ hD.ne'

/-- Directional mean-square convergence and the increment estimate imply uniform
mean-square convergence over the Euclidean unit ball. -/
theorem c5_corrector_uniform_mean_square_on_unit_ball
    {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (physicalReferenceLaw Q))
    (C : ℝ) (hC : 0 ≤ C) (hi : ∀ x y : Vec d,
      Integrable (fun ω : PhysicalField d L => euclideanNorm (χ ω x - χ ω y)^2)
        (physicalReferenceLaw Q) ∧
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x - χ ω y)^2
        ∂physicalReferenceLaw Q) ≤ C * euclideanNorm (x-y)^2)
    (hdir : ∀ y : Vec d, Tendsto (fun n : ℕ =>
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω (((n : ℝ)+1) • y))^2
        ∂physicalReferenceLaw Q) / ((n : ℝ)+1)^2) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : Vec d,
      euclideanNorm x ≤ 1 →
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω (((n : ℝ)+1) • x))^2
        ∂physicalReferenceLaw Q) / ((n : ℝ)+1)^2 ≤ ε := by
  intro ε hε
  let δ := min 1 (ε / (8 * (C+1) + 1))
  have hden : 0 < 8 * (C+1) + 1 := by positivity
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (8 * (C+1) + 1) := min_le_right _ _
  have hsmall : 2 * C * δ^2 ≤ ε / 2 := by
    have hmul := (le_div_iff₀ hden).mp hδ2
    have hsq : δ^2 ≤ δ := by nlinarith
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hsq)]
  obtain ⟨s, hs⟩ := c5_euclidean_unit_ball_finite_net hδ
  have hfinite : ∀ᶠ n : ℕ in atTop, ∀ y ∈ s,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω (((n : ℝ)+1) • y))^2
        ∂physicalReferenceLaw Q) / ((n : ℝ)+1)^2 < ε / 4 := by
    apply (eventually_all_finset s).2
    intro y hy
    exact (hdir y).eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hfinite] with n hn x hx
  obtain ⟨y, hy, hxy⟩ := hs x hx
  have ha : 0 < (n : ℝ)+1 := by positivity
  have ha2 : 0 < ((n : ℝ)+1)^2 := sq_pos_of_pos ha
  have hnxy : euclideanNorm ((((n : ℝ)+1) • x) - (((n : ℝ)+1) • y)) ≤
      ((n : ℝ)+1) * δ := by
    rw [← smul_sub, TimeChange.euclideanNorm_smul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hxy.le ha.le
  have hnxy0 : 0 ≤ euclideanNorm ((((n : ℝ)+1) • x) - (((n : ℝ)+1) • y)) :=
    Real.sqrt_nonneg _
  have hbound := c5_corrector_mean_square_nearby Q χ hmem C hi
    (((n : ℝ)+1) • x) (((n : ℝ)+1) • y)
  have hnys := hn y hy
  apply (div_le_iff₀ ha2).2
  have hybound := (div_lt_iff₀ ha2).1 hnys
  have hsquare : euclideanNorm ((((n : ℝ)+1) • x) - (((n : ℝ)+1) • y))^2 ≤
      (((n : ℝ)+1)^2) * δ^2 := by
    nlinarith [sq_nonneg (euclideanNorm ((((n : ℝ)+1) • x) - (((n : ℝ)+1) • y)) -
      ((n : ℝ)+1) * δ)]
  have hcost := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 2*C by positivity)
  have hsmall' := mul_le_mul_of_nonneg_left hsmall ha2.le
  nlinarith

/-- Uniform vanishing on scaled unit balls gives a global quadratic growth bound. -/
theorem c5_corrector_mean_square_growth_of_uniform_unit_ball
    {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hunit : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : Vec d,
      euclideanNorm x ≤ 1 →
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω (((n : ℝ)+1) • x))^2
        ∂physicalReferenceLaw Q) / ((n : ℝ)+1)^2 ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2 ∂physicalReferenceLaw Q) ≤
        C + ε * euclideanNorm x^2 := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunit (ε / 2) (by linarith))
  refine ⟨ε * ((N : ℝ) + 2)^2, by positivity, ?_⟩
  intro x
  let a : ℝ := euclideanNorm x
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  let n : ℕ := N + Nat.ceil a
  let t : ℝ := (n : ℝ) + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have ha_le : a ≤ t := by
    have hc := Nat.le_ceil a
    dsimp [t, n]
    push_cast
    linarith
  have ht_le : t ≤ (N : ℝ) + 2 + a := by
    have hc := (Nat.ceil_lt_add_one ha).le
    dsimp [t, n]
    push_cast
    linarith
  let z : Vec d := t⁻¹ • x
  have hz : euclideanNorm z ≤ 1 := by
    dsimp [z]
    rw [TimeChange.euclideanNorm_smul, abs_of_nonneg (inv_nonneg.mpr ht.le)]
    change t⁻¹ * a ≤ 1
    exact (inv_mul_le_one₀ ht).2 ha_le
  have hnt : N ≤ n := Nat.le_add_right _ _
  have hh := hN n hnt z hz
  have htz : t • z = x := by
    dsimp [z]
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  change (∫ ω : PhysicalField d L, euclideanNorm (χ ω (t • z))^2
      ∂physicalReferenceLaw Q) / t^2 ≤ ε / 2 at hh
  rw [htz] at hh
  have h := (div_le_iff₀ (sq_pos_of_pos ht)).mp hh
  have hsq : t^2 ≤ 2 * (((N : ℝ)+2)^2 + a^2) := by
    have hN0 : 0 ≤ (N : ℝ) + 2 := by positivity
    nlinarith [sq_nonneg ((N : ℝ) + 2 - a)]
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ε / 2 by positivity)
  dsimp [a] at hmul
  nlinarith

theorem exists_physical_canonical_corrector_with_mean_sublinearity
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) ∧
      (∀ y : Vec d, ∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        ∀ x : Vec d, χ (translate y ω.1) x = χ ω (y+x)-χ ω y) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d,
        (∫ ω : ReductionImageV3.PhysicalField d L, euclideanNorm (χ ω x)^2
          ∂(ReductionImageV3.physicalReferenceLaw Q)) ≤ C + ε * euclideanNorm x^2) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Vec d,
       Integrable (fun ω : PhysicalField d L =>
        (euclideanNorm (χ ω x-χ ω y))^2) (ReductionImageV3.physicalReferenceLaw Q) ∧
       (∫ ω : PhysicalField d L, (euclideanNorm (χ ω x-χ ω y))^2
        ∂(ReductionImageV3.physicalReferenceLaw Q)) ≤ C*(euclideanNorm (x-y))^2 := by
  obtain ⟨χ, hm, ha, hcoc, C, hC, hi⟩ :=
    exists_physical_l2_corrector_with_stationary_cocycle Q
  have hz : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q, χ ω 0 = 0 :=
    ha.mono fun _ h => h.2.1
  have hsub : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      χ ω 0 = 0 ∧ ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ z, euclideanNorm z ≤ (t+1)*R → euclideanNorm (χ ω z)/(t+1) ≤ ε :=
    ha.mono fun _ h => ⟨h.2.1, h.2.2.1⟩
  have hmem := c5_physical_corrector_value_memLp Q χ hm hz (fun x y => (hi x y).1)
  have hcoord := c5_physical_corrector_coordinate_memLp Q χ hm hmem
  have hdir (x : Vec d) : Tendsto (fun n : ℕ =>
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω (((n : ℝ)+1) • x))^2
        ∂physicalReferenceLaw Q) / ((n : ℝ)+1)^2) atTop (𝓝 0) := by
    have ht (i : Fin d) : Tendsto (fun n : ℕ => ∫ ω : PhysicalField d L,
        (χ ω (((n : ℝ)+1) • x) i / ((n : ℝ)+1))^2 ∂physicalReferenceLaw Q)
        atTop (𝓝 0) := by
      let hf := hcoord x i
      exact c5_physical_corrector_coordinate_mean_tendsto_zero Q χ x i
        (hf.toLp _) hf.coeFn_toLp hsub hcoc
    have hs := tendsto_finset_sum Finset.univ (fun i _ => ht i)
    simp only [Finset.sum_const_zero] at hs
    apply hs.congr'
    filter_upwards with n
    have hint (i : Fin d) : Integrable (fun ω : PhysicalField d L =>
        (χ ω (((n : ℝ)+1) • x) i / ((n : ℝ)+1))^2) (physicalReferenceLaw Q) := by
      simpa only [Real.norm_eq_abs, sq_abs, div_eq_mul_inv] using
        ((hcoord (((n : ℝ)+1) • x) i).mul_const (((n : ℝ)+1)⁻¹)).norm.integrable_sq
    rw [← integral_finsetSum _ (fun i _ => hint i), ← integral_div]
    apply integral_congr_ae
    filter_upwards with ω
    rw [← TimeChange.euclideanSq_eq_sq_euclideanNorm]
    simp only [euclideanSq, dot, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_pow, pow_two, div_mul_div_comm]
  have hunit := c5_corrector_uniform_mean_square_on_unit_ball Q χ hmem C hC hi hdir
  have hgrowth := c5_corrector_mean_square_growth_of_uniform_unit_ball Q χ hunit
  exact ⟨χ, hm, ha, hcoc, hgrowth, C, hC, hi⟩

end EinsteinFull
