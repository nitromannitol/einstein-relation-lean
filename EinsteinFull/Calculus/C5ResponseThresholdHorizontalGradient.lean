import EinsteinFull.Calculus.ComplexRadialGeneratorSupport

import Mathlib.Topology.UniformSpace.UniformApproximation

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Isometric translation orbits converge uniformly when their vectors converge.
This uses no finiteness hypothesis on the stationary measure. -/
private theorem threshold_orbit_tendstoUniformly
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ} (j : Fin d)
    {ι : Type*} {l : Filter ι} {u : ι → Lp ℂ 2 μ} {v : Lp ℂ 2 μ}
    (hu : Tendsto u l (𝓝 v)) :
    TendstoUniformly (fun n (t : ℝ) => complexTranslation μ hμ (t • unitVector j) (u n))
      (fun t : ℝ => complexTranslation μ hμ (t • unitVector j) v) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hu ε hε] with n hn t
  simpa only [dist_eq_norm, ← map_sub, norm_complexTranslation, norm_sub_rev] using hn

/-- A vector in the strong horizontal derivative domain has a continuous orbit. -/
private theorem threshold_continuous_orbit_of_derivative
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ} {j : Fin d}
    {f g : Lp ℂ 2 μ} (hf : HasComplexHorizontalDerivative μ hμ j f g) :
    Continuous (fun t : ℝ => complexTranslation μ hμ (t • unitVector j) f) :=
  continuous_iff_continuousAt.mpr fun t => (hf.hasDerivAt_orbit t).continuousAt

/-- The derivative vector also has a continuous orbit, even for an infinite measure. -/
private theorem threshold_continuous_derivative_orbit
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ} {j : Fin d}
    {f g : Lp ℂ 2 μ} (hf : HasComplexHorizontalDerivative μ hμ j f g) :
    Continuous (fun t : ℝ => complexTranslation μ hμ (t • unitVector j) g) := by
  have hlim := threshold_orbit_tendstoUniformly (hμ := hμ) j hf
  apply hlim.continuous
  apply Eventually.frequently
  apply Eventually.of_forall
  intro s
  have hc := threshold_continuous_orbit_of_derivative hf
  have hshift : Continuous (fun t : ℝ =>
      complexTranslation μ hμ (t • unitVector j)
        (complexTranslation μ hμ (s • unitVector j) f)) := by
    have h := hc.comp (continuous_id.add_const s)
    change Continuous (fun t : ℝ => complexTranslation μ hμ ((t + s) • unitVector j) f) at h
    simpa only [Function.comp_apply, id_eq, add_smul, complexTranslation_add] using h
  have h := (hshift.sub hc).const_smul ((s : ℂ)⁻¹)
  change Continuous (fun t : ℝ => (s : ℂ)⁻¹ •
    (complexTranslation μ hμ (t • unitVector j)
      (complexTranslation μ hμ (s • unitVector j) f) -
        complexTranslation μ hμ (t • unitVector j) f)) at h
  simpa only [map_smul, map_sub] using h

/-- Integrated horizontal differentiation needs continuity only of the derivative
orbit; that continuity follows from the domain relation itself. -/
private theorem threshold_integral_orbit
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ} {j : Fin d}
    {f g : Lp ℂ 2 μ} (hf : HasComplexHorizontalDerivative μ hμ j f g) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, complexTranslation μ hμ (s • unitVector j) g) =
      complexTranslation μ hμ (t • unitVector j) f - f := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => hf.hasDerivAt_orbit s)
    ((threshold_continuous_derivative_orbit hf).intervalIntegrable 0 t)
  simpa only [zero_smul, complexTranslation_zero] using h

/-- Strong L2 approximation preserves horizontal derivatives for any stationary
measure. No probability assumption is needed on the approximating domain. -/
theorem response_horizontal_derivative_of_tendsto
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ} {j : Fin d}
    {f g : ℕ → Lp ℂ 2 μ} {v w : Lp ℂ 2 μ}
    (hfg : ∀ n, HasComplexHorizontalDerivative μ hμ j (f n) (g n))
    (hf : Tendsto f atTop (𝓝 v)) (hg : Tendsto g atTop (𝓝 w)) :
    HasComplexHorizontalDerivative μ hμ j v w := by
  have hw : Continuous (fun t : ℝ => complexTranslation μ hμ (t • unitVector j) w) :=
    (threshold_orbit_tendstoUniformly (hμ := hμ) j hg).continuous
      (Eventually.frequently (Eventually.of_forall fun n =>
        threshold_continuous_derivative_orbit (hfg n)))
  have hI (t : ℝ) :
      Tendsto (fun n => ∫ s in (0 : ℝ)..t,
        complexTranslation μ hμ (s • unitVector j) (g n)) atTop
        (𝓝 (∫ s in (0 : ℝ)..t, complexTranslation μ hμ (s • unitVector j) w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (show Tendsto (fun n => |t| * ‖g n - w‖) atTop (𝓝 0) from ?_)
    · rw [← intervalIntegral.integral_sub
        ((threshold_continuous_derivative_orbit (hfg n)).intervalIntegrable 0 t)
        (hw.intervalIntegrable 0 t)]
      simpa only [← map_sub, sub_zero, mul_comm] using
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := t)
          (fun s _ => le_of_eq (norm_complexTranslation μ hμ
            (s • unitVector j) (g n - w))))
    · simpa only [sub_self, norm_zero, mul_zero] using (hg.sub_const w).norm.const_mul |t|
  have hid (t : ℝ) :
      (∫ s in (0 : ℝ)..t, complexTranslation μ hμ (s • unitVector j) w) =
        complexTranslation μ hμ (t • unitVector j) v - v := by
    have hR := (((complexTranslation μ hμ (t • unitVector j)).continuous.tendsto v).comp hf).sub hf
    have hL := hI t
    simp only [threshold_integral_orbit (hfg _) t] at hL
    exact tendsto_nhds_unique hL hR
  have hd := (hw.integral_hasStrictDerivAt 0 0).hasDerivAt
  simp only [zero_smul, complexTranslation_zero] at hd
  have he : (fun t => ∫ s in (0 : ℝ)..t,
      complexTranslation μ hμ (s • unitVector j) w) =
      fun t => complexTranslation μ hμ (t • unitVector j) v - v := funext hid
  rw [he, hasDerivAt_iff_tendsto_slope_zero] at hd
  unfold HasComplexHorizontalDerivative
  simp only [← Complex.ofReal_inv, Complex.coe_smul]
  simp only [zero_add, zero_smul, complexTranslation_zero, sub_self, sub_zero] at hd
  exact hd

/-- The preceding arbitrary-measure closure holds in every horizontal direction. -/
theorem response_horizontal_gradient_of_tendsto
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ}
    {f : ℕ → Lp ℂ 2 μ} {G : ℕ → Fin d → Lp ℂ 2 μ}
    {v : Lp ℂ 2 μ} {H : Fin d → Lp ℂ 2 μ}
    (hG : ∀ n, HasComplexHorizontalGradient μ hμ (f n) (G n))
    (hf : Tendsto f atTop (𝓝 v))
    (hH : ∀ j, Tendsto (fun n => G n j) atTop (𝓝 (H j))) :
    HasComplexHorizontalGradient μ hμ v H :=
  fun j => response_horizontal_derivative_of_tendsto (fun n => hG n j) hf (hH j)

/-- A rational regularization of the zero-threshold radial weight. -/
private def thresholdZeroWeight (ε s : ℝ) : ℝ := s / (ε + s)

private def thresholdZeroSlope (ε s : ℝ) : ℝ := ε / (ε + s) ^ 2

private theorem thresholdZeroWeight_hasDerivAt {ε s : ℝ}
    (hε : 0 < ε) (hs : 0 ≤ s) :
    HasDerivAt (thresholdZeroWeight ε) (thresholdZeroSlope ε s) s := by
  have hden : ε + s ≠ 0 := (add_pos_of_pos_of_nonneg hε hs).ne'
  convert (hasDerivAt_id s).div ((hasDerivAt_id s).const_add ε) hden using 1
  · rfl
  · dsimp only [thresholdZeroSlope, id_eq]
    ring

private theorem thresholdZeroWeight_bound {ε s : ℝ}
    (hε : 0 < ε) (hs : 0 ≤ s) :
    |thresholdZeroWeight ε s| + 2 * |thresholdZeroSlope ε s| * s ≤ 3 := by
  have hden : 0 < ε + s := add_pos_of_pos_of_nonneg hε hs
  have hw : 0 ≤ thresholdZeroWeight ε s := div_nonneg hs hden.le
  have hd : 0 ≤ thresholdZeroSlope ε s := div_nonneg hε.le (sq_nonneg _)
  have hw1 : thresholdZeroWeight ε s ≤ 1 :=
    (div_le_one hden).mpr (le_add_of_nonneg_left hε.le)
  have hd1 : thresholdZeroSlope ε s * s ≤ 1 := by
    unfold thresholdZeroSlope
    rw [div_mul_eq_mul_div, div_le_one (sq_pos_of_pos hden)]
    nlinarith only [sq_nonneg ε, sq_nonneg s, mul_nonneg hε.le hs]
  rw [abs_of_nonneg hw, abs_of_nonneg hd]
  linarith only [hw1, hd1]

private theorem thresholdZeroWeight_continuousOn {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (thresholdZeroWeight ε) (Set.Ici 0) ∧
      ContinuousOn (thresholdZeroSlope ε) (Set.Ici 0) := by
  have hden (s : ℝ) (hs : s ∈ Set.Ici (0 : ℝ)) : ε + s ≠ 0 :=
    (add_pos_of_pos_of_nonneg hε hs).ne'
  exact ⟨continuousOn_id.div (continuousOn_const.add continuousOn_id) hden,
    continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
      (fun s hs => pow_ne_zero 2 (hden s hs))⟩

private theorem thresholdZeroWeight_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε => thresholdZeroWeight ε s) (𝓝 (0 : ℝ)) (𝓝 1) ∧
      Tendsto (fun ε => thresholdZeroSlope ε s) (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hden := (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).add_const s
  change Tendsto (fun ε : ℝ => ε + s) (𝓝 0) (𝓝 (0 + s)) at hden
  rw [zero_add] at hden
  constructor
  · have h := (tendsto_const_nhds (x := s)).div hden hs.ne'
    change Tendsto (fun ε : ℝ => thresholdZeroWeight ε s) (𝓝 0) (𝓝 (s / s)) at h
    simpa only [div_self hs.ne'] using h
  · have h := (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).div
      (hden.pow 2) (pow_ne_zero 2 hs.ne')
    change Tendsto (fun ε : ℝ => thresholdZeroSlope ε s) (𝓝 0) (𝓝 (0 / s ^ 2)) at h
    simpa only [zero_div] using h

private theorem thresholdZeroDifferential_tendsto (z w : ℂ) :
    Tendsto (fun ε : ℝ =>
        complexRadialDifferential (thresholdZeroWeight ε (‖z‖ ^ 2))
          (thresholdZeroSlope ε (‖z‖ ^ 2)) z w)
      (𝓝 0) (𝓝 (if 0 < ‖z‖ then w else 0)) := by
  by_cases hz : z = 0
  · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), thresholdZeroWeight,
      zero_div, complexRadialDifferential_apply, zero_smul, smul_zero, add_zero,
      lt_self_iff_false, ↓reduceIte]
    exact tendsto_const_nhds
  · have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hl := thresholdZeroWeight_tendsto (sq_pos_of_pos hnorm)
    have h := (hl.1.smul_const w).add
      ((((tendsto_const_nhds (x := (2 : ℝ))).mul hl.2).mul_const
        (inner ℝ z w)).smul_const z)
    simpa only [complexRadialDifferential_apply, one_smul, mul_zero, zero_mul,
      zero_smul, add_zero, ite_eq_left hnorm] using h

/-- C1 zero-threshold approximations are admissible in the actual stationary H1
space, with their literal radial differential and a uniform derivative bound. -/
private theorem threshold_zero_approximation
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ}
    {f : Lp ℂ 2 μ} {G : Fin d → Lp ℂ 2 μ}
    (hG : HasComplexHorizontalGradient μ hμ f G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : Lp ℂ 2 μ) (H : Fin d → Lp ℂ 2 μ),
      (v =ᵐ[μ] fun a => thresholdZeroWeight ε (‖f a‖ ^ 2) • f a) ∧
      HasComplexHorizontalGradient μ hμ v H ∧
      (∀ j, H j =ᵐ[μ] fun a =>
        complexRadialDifferential (thresholdZeroWeight ε (‖f a‖ ^ 2))
          (thresholdZeroSlope ε (‖f a‖ ^ 2)) (f a) (G j a)) := by
  have hc := thresholdZeroWeight_continuousOn hε
  have h := hG.comp_radial (K := (3 : ℝ≥0)) hc.1 hc.2
    (fun s hs => thresholdZeroWeight_hasDerivAt hε hs)
    (fun s hs => thresholdZeroWeight_bound hε hs)
  obtain ⟨H, hH, hrep⟩ := h
  exact ⟨_, H, LipschitzWith.coeFn_compLp _ _ _, hH, hrep⟩

/-- Horizontal gradients vanish almost everywhere where their function vanishes.
The proof uses C1 radial approximations and strong closure, for arbitrary
stationary measures, including infinite ones. -/
theorem response_horizontal_gradient_zero_on_zero
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ}
    {f : Lp ℂ 2 μ} {G : Fin d → Lp ℂ 2 μ}
    (hG : HasComplexHorizontalGradient μ hμ f G) :
    ∀ j, ∀ᵐ a ∂μ, f a = 0 → G j a = 0 := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose u A hu hA hrep using fun n => threshold_zero_approximation hG (hε n)
  let P (j : Fin d) (a : FieldPair d) : ℂ := if 0 < ‖f a‖ then G j a else 0
  have hset : MeasurableSet {a : FieldPair d | 0 < ‖f a‖} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).measurable.norm
  have hP (j : Fin d) : MemLp (P j) 2 μ := by
    have hi := (Lp.memLp (G j)).indicator hset
    change MemLp (P j) 2 μ at hi
    exact hi
  let H (j : Fin d) : Lp ℂ 2 μ := (hP j).toLp (P j)
  have hHrep (j : Fin d) : H j =ᵐ[μ] P j := (hP j).coeFn_toLp
  have hPnorm (j : Fin d) (a : FieldPair d) : ‖P j a‖ ≤ ‖G j a‖ := by
    dsimp only [P]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (G j a)
  have hw (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
      0 ≤ thresholdZeroWeight (ε n) s ∧ thresholdZeroWeight (ε n) s ≤ 1 := by
    have hd : 0 < ε n + s := add_pos_of_pos_of_nonneg (hε n) hs
    exact ⟨div_nonneg hs hd.le,
      (div_le_one hd).mpr (le_add_of_nonneg_left (hε n).le)⟩
  have hDnorm (n : ℕ) (a : FieldPair d) (w : ℂ) :
      ‖complexRadialDifferential (thresholdZeroWeight (ε n) (‖f a‖ ^ 2))
          (thresholdZeroSlope (ε n) (‖f a‖ ^ 2)) (f a) w‖ ≤ 3 * ‖w‖ := by
    apply ContinuousLinearMap.le_of_opNorm_le
    exact (norm_complexRadialDifferential_le _ _ _).trans
      (thresholdZeroWeight_bound (hε n) (sq_nonneg _))
  have hulim : Tendsto u atTop (𝓝 f) := by
    apply tendsto_complexLp_of_dominated hu (Filter.EventuallyEq.rfl)
      (b := fun a => 2 * ‖f a‖)
    · convert ((Lp.memLp f).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul
        ((2 : ℝ) ^ 2) using 1
      ext a
      ring
    · exact Eventually.of_forall fun n => Eventually.of_forall fun a => by
        calc
          ‖thresholdZeroWeight (ε n) (‖f a‖ ^ 2) • f a - f a‖ ≤
              ‖thresholdZeroWeight (ε n) (‖f a‖ ^ 2) • f a‖ + ‖f a‖ :=
            norm_sub_le _ _
          _ ≤ ‖f a‖ + ‖f a‖ := by
            gcongr
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw n _ (sq_nonneg _)).1]
            exact mul_le_of_le_one_left (norm_nonneg _) (hw n _ (sq_nonneg _)).2
          _ = _ := by ring
    · exact Eventually.of_forall fun a => by
        by_cases ha : f a = 0
        · simp only [ha, smul_zero]
          exact tendsto_const_nhds
        · have hnorm : 0 < ‖f a‖ := norm_pos_iff.mpr ha
          have h := ((thresholdZeroWeight_tendsto (sq_pos_of_pos hnorm)).1.comp hεlim).smul_const
            (f a)
          change Tendsto (fun n => thresholdZeroWeight (ε n) (‖f a‖ ^ 2) • f a)
            atTop (𝓝 ((1 : ℝ) • f a)) at h
          simpa only [one_smul] using h
  have hAlim (j : Fin d) : Tendsto (fun n => A n j) atTop (𝓝 (H j)) := by
    apply tendsto_complexLp_of_dominated (fun n => hrep n j) (hHrep j)
      (b := fun a => 4 * ‖G j a‖)
    · convert ((Lp.memLp (G j)).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul
        ((4 : ℝ) ^ 2) using 1
      ext a
      ring
    · exact Eventually.of_forall fun n => Eventually.of_forall fun a => by
        calc
          _ ≤ ‖complexRadialDifferential (thresholdZeroWeight (ε n) (‖f a‖ ^ 2))
              (thresholdZeroSlope (ε n) (‖f a‖ ^ 2)) (f a) (G j a)‖ + ‖P j a‖ :=
            norm_sub_le _ _
          _ ≤ 3 * ‖G j a‖ + ‖G j a‖ := add_le_add (hDnorm n a _) (hPnorm j a)
          _ = _ := by ring
    · exact Eventually.of_forall fun a =>
        (thresholdZeroDifferential_tendsto (f a) (G j a)).comp hεlim
  have hH := response_horizontal_gradient_of_tendsto hA hulim hAlim
  intro j
  have heq : G j = H j := (hG j).unique (hH j)
  filter_upwards [hHrep j] with a ha
  rw [← heq] at ha
  intro hz
  simpa only [P, hz, norm_zero, lt_self_iff_false, ↓reduceIte] using ha

/-- The requested threshold formula at threshold zero, including the zero level
set of the L2 representative. -/
theorem response_threshold_horizontal_gradient_zero
    {d : ℕ} (μ : Measure (FieldPair d)) (hμ : IsStationary μ)
    (f : Lp ℂ 2 μ) (G : Fin d → Lp ℂ 2 μ)
    (hG : HasComplexHorizontalGradient μ hμ f G) :
    ∃ (v : Lp ℂ 2 μ) (H : Fin d → Lp ℂ 2 μ),
      (v =ᵐ[μ] fun a => ((max (‖f a‖ - 0) 0 / ‖f a‖ : ℝ) : ℂ) * f a) ∧
      HasComplexHorizontalGradient μ hμ v H ∧
      ∀ j : Fin d, H j =ᵐ[μ] fun a =>
        if 0 < ‖f a‖ then
          (((1 - 0 / ‖f a‖ : ℝ) : ℂ) * G j a +
            ((0 / ‖f a‖ ^ 3 * (star (f a) * G j a).re : ℝ) : ℂ) * f a)
        else 0 := by
  refine ⟨f, G, Eventually.of_forall fun a => ?_, hG, ?_⟩
  · by_cases ha : f a = 0
    · simp only [ha, mul_zero]
    · simp only [sub_zero, max_eq_left (norm_nonneg _), div_self (norm_ne_zero_iff.mpr ha),
        Complex.ofReal_one, one_mul]
  · intro j
    filter_upwards [response_horizontal_gradient_zero_on_zero hG j] with a ha
    by_cases hnorm : 0 < ‖f a‖
    · simp only [ite_eq_left hnorm, zero_div, sub_zero, Complex.ofReal_one, one_mul,
        zero_mul, Complex.ofReal_zero, add_zero]
    · rw [ite_eq_right hnorm]
      exact ha (norm_eq_zero.mp (le_antisymm (le_of_not_gt hnorm) (norm_nonneg _)))


private def thresholdExteriorWeight (K ε s : ℝ) : ℝ :=
  (1 - K / Real.sqrt s) * ((s - K ^ 2) / (s - K ^ 2 + ε))

private def thresholdExteriorSlope (K ε s : ℝ) : ℝ :=
  K / (2 * Real.sqrt s ^ 3) * ((s - K ^ 2) / (s - K ^ 2 + ε)) +
    (1 - K / Real.sqrt s) * (ε / (s - K ^ 2 + ε) ^ 2)

private def thresholdWeight (K ε s : ℝ) : ℝ :=
  if s ≤ K ^ 2 then 0 else thresholdExteriorWeight K ε s

private def thresholdSlope (K ε s : ℝ) : ℝ :=
  if s ≤ K ^ 2 then 0 else thresholdExteriorSlope K ε s

private theorem thresholdExterior_hasDerivAt {K ε s : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (hs : K ^ 2 ≤ s) :
    HasDerivAt (thresholdExteriorWeight K ε) (thresholdExteriorSlope K ε s) s := by
  have hspos : 0 < s := (sq_pos_of_pos hK).trans_le hs
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hspos).ne'
  have hd : s - K ^ 2 + ε ≠ 0 := (add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs) hε).ne'
  have hroot := Real.hasDerivAt_sqrt hspos.ne'
  have hleft := (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_const s K).div hroot hr)
  have hright := ((hasDerivAt_id s).sub_const (K ^ 2)).div
    (((hasDerivAt_id s).sub_const (K ^ 2)).add_const ε) hd
  convert hleft.mul hright using 1
  · rfl
  · dsimp [thresholdExteriorSlope]
    field_simp [hr, hd]
    ring

private theorem thresholdExterior_boundary {K ε : ℝ} (hK : 0 < K) :
    thresholdExteriorWeight K ε (K ^ 2) = 0 ∧
      thresholdExteriorSlope K ε (K ^ 2) = 0 := by
  constructor <;> simp only [thresholdExteriorWeight, thresholdExteriorSlope,
    Real.sqrt_sq hK.le, div_self hK.ne', sub_self, zero_div, mul_zero,
    zero_mul, add_zero]

private theorem thresholdWeight_hasDerivAt {K ε s : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    HasDerivAt (thresholdWeight K ε) (thresholdSlope K ε s) s := by
  rcases lt_trichotomy s (K ^ 2) with hs | rfl | hs
  · rw [thresholdSlope, ite_eq_left hs.le]
    apply (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hs] with t ht
    exact ite_eq_left ht.le
  · rw [thresholdSlope, ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (thresholdWeight K ε) 0 (Set.Iic (K ^ 2)) (K ^ 2) := by
      apply ((hasDerivAt_const (K ^ 2) (0 : ℝ)).hasDerivWithinAt
        (s := Set.Iic (K ^ 2))).congr_of_mem
      · intro t ht
        exact ite_eq_left ht
      · exact (show K ^ 2 ≤ K ^ 2 from le_rfl)
    have hr : HasDerivWithinAt (thresholdWeight K ε) 0 (Set.Ici (K ^ 2)) (K ^ 2) := by
      have he : HasDerivWithinAt (thresholdExteriorWeight K ε)
          (thresholdExteriorSlope K ε (K ^ 2)) (Set.Ici (K ^ 2)) (K ^ 2) :=
        (thresholdExterior_hasDerivAt hK hε le_rfl).hasDerivWithinAt
      rw [(thresholdExterior_boundary hK).2] at he
      apply he.congr_of_mem
      · intro t ht
        by_cases heq : t = K ^ 2
        · subst t
          simp only [thresholdWeight, ite_eq_left le_rfl, (thresholdExterior_boundary hK).1]
        · exact ite_eq_right (not_le.mpr (lt_of_le_of_ne ht (Ne.symm heq)))
      · exact (show K ^ 2 ≤ K ^ 2 from le_rfl)
    have h := hl.union hr
    rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h
    exact h
  · rw [thresholdSlope, ite_eq_right (not_le.mpr hs)]
    apply (thresholdExterior_hasDerivAt hK hε hs.le).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hs] with t ht
    exact ite_eq_right (not_le.mpr ht)

private theorem thresholdExteriorSlope_continuousOn {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    ContinuousOn (thresholdExteriorSlope K ε) (Set.Ici (K ^ 2)) := by
  have hr (s : ℝ) (hs : s ∈ Set.Ici (K ^ 2)) : Real.sqrt s ≠ 0 :=
    (Real.sqrt_pos.mpr ((sq_pos_of_pos hK).trans_le hs)).ne'
  have hd (s : ℝ) (hs : s ∈ Set.Ici (K ^ 2)) : s - K ^ 2 + ε ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs) hε).ne'
  exact ((continuousOn_const.div
    (continuousOn_const.mul (Real.continuous_sqrt.continuousOn.pow 3))
      (fun s hs => mul_ne_zero (by norm_num) (pow_ne_zero 3 (hr s hs)))).mul
    ((continuousOn_id.sub continuousOn_const).div
      ((continuousOn_id.sub continuousOn_const).add continuousOn_const) hd)).add
    ((continuousOn_const.sub (continuousOn_const.div Real.continuous_sqrt.continuousOn hr)).mul
      (continuousOn_const.div
        (((continuousOn_id.sub continuousOn_const).add continuousOn_const).pow 2)
        (fun s hs => pow_ne_zero 2 (hd s hs))))

private theorem threshold_continuous {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    Continuous (thresholdWeight K ε) ∧ Continuous (thresholdSlope K ε) := by
  refine ⟨continuous_iff_continuousAt.mpr (fun s =>
    (thresholdWeight_hasDerivAt hK hε (s := s)).continuousAt), ?_⟩
  apply continuous_if_le continuous_id continuous_const continuousOn_const
    (thresholdExteriorSlope_continuousOn hK hε)
  intro s hs
  change s = K ^ 2 at hs
  subst s
  exact (thresholdExterior_boundary hK).2.symm


private theorem thresholdWeight_bound {K ε s : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    (0 ≤ thresholdWeight K ε s ∧ thresholdWeight K ε s ≤ 1) ∧
      |thresholdWeight K ε s| + 2 * |thresholdSlope K ε s| * s ≤ 3 := by
  by_cases hs : s ≤ K ^ 2
  · simp only [thresholdWeight, thresholdSlope, ite_eq_left hs, abs_zero,
      mul_zero, zero_mul, add_zero]
    norm_num
  have hgap : 0 < s - K ^ 2 := sub_pos.mpr (lt_of_not_ge hs)
  have hspos : 0 < s := (sq_pos_of_pos hK).trans (lt_of_not_ge hs)
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hrs : Real.sqrt s ^ 2 = s := Real.sq_sqrt hspos.le
  have hKr : K ≤ Real.sqrt s := Real.le_sqrt_of_sq_le (le_of_not_ge hs)
  have hd : 0 < s - K ^ 2 + ε := add_pos hgap hε
  have ha : 0 ≤ 1 - K / Real.sqrt s := sub_nonneg.mpr ((div_le_one hr).mpr hKr)
  have ha1 : 1 - K / Real.sqrt s ≤ 1 := sub_le_self _ (div_nonneg hK.le hr.le)
  have ht : 0 ≤ (s - K ^ 2) / (s - K ^ 2 + ε) := div_nonneg hgap.le hd.le
  have ht1 : (s - K ^ 2) / (s - K ^ 2 + ε) ≤ 1 :=
    (div_le_one hd).mpr (le_add_of_nonneg_right hε.le)
  have hw : 0 ≤ thresholdExteriorWeight K ε s := mul_nonneg ha ht
  have hw1 : thresholdExteriorWeight K ε s ≤ 1 := by
    exact (mul_le_mul ha1 ht1 ht (by norm_num)).trans_eq (mul_one 1)
  have hc : 0 ≤ thresholdExteriorSlope K ε s := by
    exact add_nonneg (mul_nonneg (div_nonneg hK.le (by positivity)) ht)
      (mul_nonneg ha (div_nonneg hε.le (sq_nonneg _)))
  have hsa : s * (1 - K / Real.sqrt s) ≤ s - K ^ 2 := by
    have heq : s * (1 - K / Real.sqrt s) = Real.sqrt s * (Real.sqrt s - K) := by
      generalize hroot : Real.sqrt s = r at *
      rw [← hrs]
      field_simp [hr.ne']
    rw [heq]
    nlinarith only [hrs, mul_nonneg hK.le (sub_nonneg.mpr hKr)]
  have hsq : (s - K ^ 2) * ε ≤ (s - K ^ 2 + ε) ^ 2 := by
    nlinarith only [sq_nonneg (s - K ^ 2), sq_nonneg ε,
      mul_nonneg hgap.le hε.le]
  have heq : thresholdExteriorWeight K ε s + 2 * thresholdExteriorSlope K ε s * s =
      (s - K ^ 2) / (s - K ^ 2 + ε) +
        2 * (s * (1 - K / Real.sqrt s)) * ε / (s - K ^ 2 + ε) ^ 2 := by
    dsimp only [thresholdExteriorWeight, thresholdExteriorSlope]
    generalize hroot : Real.sqrt s = r at *
    rw [← hrs]
    field_simp [hr.ne', hd.ne']
    ring
  have hterm : (s * (1 - K / Real.sqrt s)) * ε / (s - K ^ 2 + ε) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hd)]
    exact (mul_le_mul_of_nonneg_right hsa hε.le).trans hsq
  simp only [thresholdWeight, thresholdSlope, ite_eq_right hs]
  refine ⟨⟨hw, hw1⟩, ?_⟩
  rw [abs_of_nonneg hw, abs_of_nonneg hc, heq]
  calc
    _ = (s - K ^ 2) / (s - K ^ 2 + ε) +
        2 * ((s * (1 - K / Real.sqrt s)) * ε / (s - K ^ 2 + ε) ^ 2) := by ring
    _ ≤ 1 + 2 * 1 := add_le_add ht1 (mul_le_mul_of_nonneg_left hterm (by norm_num))
    _ = 3 := by norm_num


private theorem thresholdExterior_tendsto {K s : ℝ} (hs : K ^ 2 < s) :
    Tendsto (fun ε => thresholdExteriorWeight K ε s) (𝓝 (0 : ℝ))
        (𝓝 (1 - K / Real.sqrt s)) ∧
      Tendsto (fun ε => thresholdExteriorSlope K ε s) (𝓝 (0 : ℝ))
        (𝓝 (K / (2 * Real.sqrt s ^ 3))) := by
  have ht : 0 < s - K ^ 2 := sub_pos.mpr hs
  have hd : Tendsto (fun ε : ℝ => s - K ^ 2 + ε) (𝓝 0) (𝓝 (s - K ^ 2)) := by
    have h := (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).const_add (s - K ^ 2)
    change Tendsto (fun ε : ℝ => s - K ^ 2 + ε) (𝓝 0) (𝓝 (s - K ^ 2 + 0)) at h
    simpa only [add_zero] using h
  have hfrac : Tendsto (fun ε : ℝ => (s - K ^ 2) / (s - K ^ 2 + ε))
      (𝓝 0) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := s - K ^ 2)).div hd ht.ne'
    change Tendsto (fun ε : ℝ => (s - K ^ 2) / (s - K ^ 2 + ε))
      (𝓝 0) (𝓝 ((s - K ^ 2) / (s - K ^ 2))) at h
    simpa only [div_self ht.ne'] using h
  have hsmall : Tendsto (fun ε : ℝ => ε / (s - K ^ 2 + ε) ^ 2) (𝓝 0) (𝓝 0) := by
    have h := (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).div
      (hd.pow 2) (pow_ne_zero 2 ht.ne')
    change Tendsto (fun ε : ℝ => ε / (s - K ^ 2 + ε) ^ 2)
      (𝓝 0) (𝓝 (0 / (s - K ^ 2) ^ 2)) at h
    simpa only [zero_div] using h
  constructor
  · simpa only [thresholdExteriorWeight, mul_one] using
      hfrac.const_mul (1 - K / Real.sqrt s)
  · simpa only [thresholdExteriorSlope, mul_one, mul_zero, add_zero] using
      (hfrac.const_mul (K / (2 * Real.sqrt s ^ 3))).add
        (hsmall.const_mul (1 - K / Real.sqrt s))

private theorem threshold_pointwise_tendsto {K : ℝ} (hK : 0 < K) (z w : ℂ) :
    Tendsto (fun ε : ℝ => thresholdWeight K ε (‖z‖ ^ 2) • z)
        (𝓝 0) (𝓝 ((max (‖z‖ - K) 0 / ‖z‖ : ℝ) • z)) ∧
      Tendsto (fun ε : ℝ =>
        complexRadialDifferential (thresholdWeight K ε (‖z‖ ^ 2))
          (thresholdSlope K ε (‖z‖ ^ 2)) z w) (𝓝 0)
        (𝓝 (if K < ‖z‖ then
          complexRadialDifferential (1 - K / ‖z‖) (K / (2 * ‖z‖ ^ 3)) z w else 0)) := by
  by_cases hn : K < ‖z‖
  · have hs : K ^ 2 < ‖z‖ ^ 2 := (sq_lt_sq₀ hK.le (norm_nonneg z)).mpr hn
    have hnorm : ‖z‖ ≠ 0 := (hK.trans hn).ne'
    obtain ⟨hb, hc⟩ := thresholdExterior_tendsto hs
    simp only [Real.sqrt_sq (norm_nonneg z)] at hb hc
    simp only [thresholdWeight, thresholdSlope, ite_eq_right hs.not_ge, ite_eq_left hn]
    constructor
    · have heq : (‖z‖ - K) / ‖z‖ = 1 - K / ‖z‖ := by
        field_simp
      rw [max_eq_left (sub_nonneg.mpr hn.le), heq]
      exact hb.smul_const z
    · have h := (hb.smul_const w).add
        ((((hc.const_mul 2).mul_const (inner ℝ z w))).smul_const z)
      simpa only [complexRadialDifferential_apply] using h
  · have hs : ‖z‖ ^ 2 ≤ K ^ 2 :=
      (sq_le_sq₀ (norm_nonneg z) hK.le).mpr (le_of_not_gt hn)
    simp only [thresholdWeight, thresholdSlope, ite_eq_left hs, ite_eq_right hn,
      max_eq_right (sub_nonpos.mpr (le_of_not_gt hn)), zero_div, zero_smul,
      complexRadialDifferential_apply, mul_zero, zero_mul, add_zero]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

/-- The positive-threshold C1 approximants belong to the actual horizontal H1 domain. -/
private theorem threshold_approximation
    {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ}
    {f : Lp ℂ 2 μ} {G : Fin d → Lp ℂ 2 μ}
    (hG : HasComplexHorizontalGradient μ hμ f G) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    ∃ (v : Lp ℂ 2 μ) (H : Fin d → Lp ℂ 2 μ),
      (v =ᵐ[μ] fun a => thresholdWeight K ε (‖f a‖ ^ 2) • f a) ∧
      HasComplexHorizontalGradient μ hμ v H ∧
      (∀ j, H j =ᵐ[μ] fun a =>
        complexRadialDifferential (thresholdWeight K ε (‖f a‖ ^ 2))
          (thresholdSlope K ε (‖f a‖ ^ 2)) (f a) (G j a)) := by
  have hc := threshold_continuous hK hε
  have h := hG.comp_radial (K := (3 : ℝ≥0)) hc.1.continuousOn hc.2.continuousOn
    (fun _ _ => thresholdWeight_hasDerivAt hK hε)
    (fun _ _ => (thresholdWeight_bound hK hε).2)
  obtain ⟨H, hH, hrep⟩ := h
  exact ⟨_, H, LipschitzWith.coeFn_compLp _ _ _, hH, hrep⟩


private theorem thresholdDifferential_eq (K : ℝ) (z w : ℂ) :
    complexRadialDifferential (1 - K / ‖z‖) (K / (2 * ‖z‖ ^ 3)) z w =
      (((1 - K / ‖z‖ : ℝ) : ℂ) * w +
        ((K / ‖z‖ ^ 3 * (star z * w).re : ℝ) : ℂ) * z) := by
  have hi : inner ℝ z w = (star z * w).re := by
    change (w * star z).re = (star z * w).re
    rw [mul_comm]
  have hc : 2 * (K / (2 * ‖z‖ ^ 3)) = K / ‖z‖ ^ 3 := by
    rw [← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [complexRadialDifferential_apply, hi, hc, Complex.real_smul]

/-- Radial soft thresholding preserves the actual stationary horizontal H1 domain,
with zero gradient on the threshold sphere and the full exterior radial formula. -/
theorem response_threshold_horizontal_gradient
    {d : ℕ} (μ : Measure (FieldPair d)) (hμ : IsStationary μ)
    (f : Lp ℂ 2 μ) (G : Fin d → Lp ℂ 2 μ)
    (hG : HasComplexHorizontalGradient μ hμ f G) (K : ℝ) (hK : 0 ≤ K) :
    ∃ (v : Lp ℂ 2 μ) (H : Fin d → Lp ℂ 2 μ),
      (v =ᵐ[μ] fun ω => ((max (‖f ω‖ - K) 0 / ‖f ω‖ : ℝ) : ℂ) * f ω) ∧
      HasComplexHorizontalGradient μ hμ v H ∧
      ∀ j : Fin d, H j =ᵐ[μ] fun ω =>
        if K < ‖f ω‖ then
          (((1 - K / ‖f ω‖ : ℝ) : ℂ) * G j ω +
            ((K / ‖f ω‖ ^ 3 * (star (f ω) * G j ω).re : ℝ) : ℂ) * f ω)
        else 0 := by
  by_cases hzero : K = 0
  · subst K
    exact response_threshold_horizontal_gradient_zero μ hμ f G hG
  have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hzero)
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose u A hu hA hrep using fun n => threshold_approximation hG hKpos (hε n)
  let F (a : FieldPair d) : ℂ := (max (‖f a‖ - K) 0 / ‖f a‖ : ℝ) • f a
  let P (j : Fin d) (a : FieldPair d) : ℂ :=
    if K < ‖f a‖ then
      complexRadialDifferential (1 - K / ‖f a‖) (K / (2 * ‖f a‖ ^ 3)) (f a) (G j a)
    else 0
  have hFpoint (a : FieldPair d) :
      Tendsto (fun n => thresholdWeight K (ε n) (‖f a‖ ^ 2) • f a)
        atTop (𝓝 (F a)) :=
    ((threshold_pointwise_tendsto hKpos (f a) 0).1).comp hεlim
  have hPpoint (j : Fin d) (a : FieldPair d) :
      Tendsto (fun n =>
        complexRadialDifferential (thresholdWeight K (ε n) (‖f a‖ ^ 2))
          (thresholdSlope K (ε n) (‖f a‖ ^ 2)) (f a) (G j a))
        atTop (𝓝 (P j a)) :=
    ((threshold_pointwise_tendsto hKpos (f a) (G j a)).2).comp hεlim
  have hFnorm (n : ℕ) (a : FieldPair d) :
      ‖thresholdWeight K (ε n) (‖f a‖ ^ 2) • f a‖ ≤ ‖f a‖ := by
    have hw := (thresholdWeight_bound (s := ‖f a‖ ^ 2) hKpos (hε n)).1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hw.2
  have hDnorm (n : ℕ) (a : FieldPair d) (w : ℂ) :
      ‖complexRadialDifferential (thresholdWeight K (ε n) (‖f a‖ ^ 2))
          (thresholdSlope K (ε n) (‖f a‖ ^ 2)) (f a) w‖ ≤ 3 * ‖w‖ := by
    apply ContinuousLinearMap.le_of_opNorm_le
    exact (norm_complexRadialDifferential_le _ _ _).trans
      (thresholdWeight_bound hKpos (hε n)).2
  have hFbound (a : FieldPair d) : ‖F a‖ ≤ ‖f a‖ :=
    le_of_tendsto (hFpoint a).norm (Eventually.of_forall fun n => hFnorm n a)
  have hPbound (j : Fin d) (a : FieldPair d) : ‖P j a‖ ≤ 3 * ‖G j a‖ :=
    le_of_tendsto (hPpoint j a).norm (Eventually.of_forall fun n => hDnorm n a (G j a))
  have hFm : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (Lp.aestronglyMeasurable (u n)).congr (hu n))
      (Eventually.of_forall hFpoint)
  have hPm (j : Fin d) : AEStronglyMeasurable (P j) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (Lp.aestronglyMeasurable (A n j)).congr (hrep n j))
      (Eventually.of_forall (hPpoint j))
  have hF : MemLp F 2 μ := by
    apply (Lp.memLp f).of_le_mul (c := 1) hFm
    exact Eventually.of_forall fun a => by simpa only [one_mul] using hFbound a
  have hP (j : Fin d) : MemLp (P j) 2 μ :=
    (Lp.memLp (G j)).of_le_mul (c := 3) (hPm j) (Eventually.of_forall (hPbound j))
  let v : Lp ℂ 2 μ := hF.toLp F
  let H (j : Fin d) : Lp ℂ 2 μ := (hP j).toLp (P j)
  have hv : v =ᵐ[μ] F := hF.coeFn_toLp
  have hHrep (j : Fin d) : H j =ᵐ[μ] P j := (hP j).coeFn_toLp
  have hulim : Tendsto u atTop (𝓝 v) := by
    apply tendsto_complexLp_of_dominated hu hv (b := fun a => 2 * ‖f a‖)
    · convert ((Lp.memLp f).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul
        ((2 : ℝ) ^ 2) using 1
      ext a
      ring
    · exact Eventually.of_forall fun n => Eventually.of_forall fun a => by
        calc
          _ ≤ ‖thresholdWeight K (ε n) (‖f a‖ ^ 2) • f a‖ + ‖F a‖ := norm_sub_le _ _
          _ ≤ ‖f a‖ + ‖f a‖ := add_le_add (hFnorm n a) (hFbound a)
          _ = _ := by ring
    · exact Eventually.of_forall hFpoint
  have hAlim (j : Fin d) : Tendsto (fun n => A n j) atTop (𝓝 (H j)) := by
    apply tendsto_complexLp_of_dominated (fun n => hrep n j) (hHrep j)
      (b := fun a => 6 * ‖G j a‖)
    · convert ((Lp.memLp (G j)).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul
        ((6 : ℝ) ^ 2) using 1
      ext a
      ring
    · exact Eventually.of_forall fun n => Eventually.of_forall fun a => by
        calc
          _ ≤ ‖complexRadialDifferential (thresholdWeight K (ε n) (‖f a‖ ^ 2))
              (thresholdSlope K (ε n) (‖f a‖ ^ 2)) (f a) (G j a)‖ + ‖P j a‖ :=
            norm_sub_le _ _
          _ ≤ 3 * ‖G j a‖ + 3 * ‖G j a‖ := add_le_add (hDnorm n a _) (hPbound j a)
          _ = _ := by ring
    · exact Eventually.of_forall (hPpoint j)
  refine ⟨v, H, ?_, response_horizontal_gradient_of_tendsto hA hulim hAlim, ?_⟩
  · simpa only [F, Complex.real_smul] using hv
  · intro j
    filter_upwards [hHrep j] with a ha
    rw [ha]
    dsimp only [P]
    split_ifs with hn
    · exact thresholdDifferential_eq K (f a) (G j a)
    · rfl

end EinsteinFull.Blueprint
