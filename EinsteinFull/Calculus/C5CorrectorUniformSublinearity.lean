import EinsteinRelation.External.AKMEnergyDensity
import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A deterministic interior consequence of a uniform Euclidean Hölder bound
and vanishing spatial L² energy. Application to the actual corrector still
requires its scale-uniform Hölder estimate. -/

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.AKM

private lemma holder_radius {d : ℕ} (α C ε : ℝ)
    (hα : 0 < α) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ((d : ℝ) + 1) * r < 1 / 2 ∧
      C * (((d : ℝ) + 1) * r) ^ α < ε / 2 := by
  have hD : 0 < (d : ℝ) + 1 := by positivity
  have hc : ContinuousAt (fun r : ℝ => C * (((d : ℝ) + 1) * r) ^ α) 0 :=
    continuousAt_const.mul
      ((continuous_const.mul continuous_id).continuousAt.rpow_const (Or.inr hα.le))
  have he : ∀ᶠ r : ℝ in 𝓝 0,
      C * (((d : ℝ) + 1) * r) ^ α < ε / 2 := by
    apply hc.eventually (gt_mem_nhds ?_)
    simpa only [mul_zero, Real.zero_rpow hα.ne', mul_zero] using half_pos hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  let r := min δ (1 / (2 * ((d : ℝ) + 1))) / 2
  have hr : 0 < r := half_pos (lt_min hδ (by positivity))
  have hrδ : r < δ := (half_lt_self (lt_min hδ (by positivity))).trans_le (min_le_left _ _)
  have hrD : r < 1 / (2 * ((d : ℝ) + 1)) :=
    (half_lt_self (lt_min hδ (by positivity))).trans_le (min_le_right _ _)
  refine ⟨r, hr, ?_, hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrδ)⟩
  have := (lt_div_iff₀ (show 0 < 2 * ((d : ℝ) + 1) by positivity)).mp hrD
  nlinarith

/-- Uniform Hölder control and spatial L² convergence imply uniform smallness
on the interior half ball, for the manuscript's explicit Euclidean norm. -/
theorem holder_l2_small_implies_uniform_small {d : ℕ} (hd : 1 ≤ d)
    (f : ℕ → Vec d → ℝ) (α C : ℝ) (hα : 0 < α) (hC : 0 ≤ C)
    (hmem : ∀ n, MemLp (f n) 2 (volume.restrict (ball (0 : Vec d) 1)))
    (hholder : ∀ n x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
      |f n x - f n y| ≤ C * euclideanNorm (x-y) ^ α)
    (hL2 : Tendsto (fun n => ∫ x in ball (0 : Vec d) 1, (f n x)^2 ∂volume)
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x, euclideanNorm x ≤ 1/2 → |f n x| ≤ ε := by
  have hD : 0 < (d : ℝ) + 1 := add_pos (Nat.cast_pos.mpr hd) zero_lt_one
  intro ε hε
  obtain ⟨r, hr, hrD, hrε⟩ := holder_radius (d := d) α C ε hα hε
  let m : ℝ := ((2 * r) ^ d)
  have hm : 0 < m := by dsimp [m]; positivity
  have he : 0 < m * (ε / 2)^2 := mul_pos hm (sq_pos_of_pos (half_pos hε))
  filter_upwards [hL2.eventually (gt_mem_nhds he)] with n hn
  intro x hx
  by_contra hxε
  have hεx : ε < |f n x| := lt_of_not_ge hxε
  have hsub : Metric.ball x r ⊆ ball (0 : Vec d) 1 := by
    intro y hy
    have hnorm : euclideanNorm (y - x) < 1 / 2 :=
      (euclideanNorm_le_dimension_mul_norm (y-x)).trans_lt
        ((mul_lt_mul_of_pos_left (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
          hD).trans hrD)
    change euclideanNorm (y - 0) < 1
    rw [sub_zero]
    have ht := TimeChange.euclideanNorm_add_le (y-x) x
    rw [sub_add_cancel] at ht
    linarith
  have hlower : ∀ y ∈ Metric.ball x r, (ε / 2)^2 ≤ (f n y)^2 := by
    intro y hy
    have hdist : ‖x-y‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
    have hh := hholder n x y (by linarith) (by
      have := hsub hy
      simpa only [ball, Set.mem_ofPred_eq, sub_zero] using this)
    have hp : C * euclideanNorm (x-y) ^ α ≤ C * (((d : ℝ) + 1) * r) ^ α :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.sqrt_nonneg _)
          ((euclideanNorm_le_dimension_mul_norm (x-y)).trans
            (mul_le_mul_of_nonneg_left hdist.le hD.le)) hα.le) hC
    have habs : ε / 2 ≤ |f n y| := by
      have ht := abs_add_le (f n x - f n y) (f n y)
      rw [sub_add_cancel] at ht
      linarith
    nlinarith [sq_abs (f n y)]
  have hi : IntegrableOn (fun y => (f n y)^2) (ball (0 : Vec d) 1) volume :=
    (hmem n).integrable_sq
  have hvol : volume.real (Metric.ball x r) = m := by
    rw [Measure.real, Real.volume_pi_ball x hr, ENNReal.toReal_ofReal]
    · simp only [Fintype.card_fin, m]
    · positivity
  have hlow := setIntegral_ge_of_const_le_real measurableSet_ball
    (measure_ball_ne_top (μ := (volume : Measure (Vec d)))) hlower (hi.mono_set hsub)
  rw [hvol] at hlow
  have hmono := setIntegral_mono_set hi (ae_of_all _ fun y => sq_nonneg (f n y))
    (ae_of_all _ fun y hy => hsub hy)
  exact (not_le_of_gt hn) (by simpa only [mul_comm] using hlow.trans hmono)

/-- Uniform spatial sublinearity makes the corrector remainder small in
probability along any family of paths tight at the same spatial scale. -/
@[nolint unusedArguments]
theorem corrector_remainder_of_uniform_sublinearity_and_tightness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (χ : Vec d → ℝ) (Z : ℕ → Ω → Vec d)
    (hχ : Continuous χ) (hZ : ∀ n, Measurable (Z n))
    (hsub : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      ∀ x, euclideanNorm x ≤ ((n : ℝ) + 1) * R → |χ x| / ((n : ℝ) + 1) ≤ ε)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | R < euclideanNorm (Z n ω) / ((n : ℝ) + 1)} ≤ ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n in Filter.atTop,
      μ {ω | ε < |χ (Z n ω)| / ((n : ℝ) + 1)} ≤ ENNReal.ofReal δ := by
  intro ε δ hε hδ
  have _hmeas : ∀ n : ℕ,
      MeasurableSet {ω | ε < |χ (Z n ω)| / ((n : ℝ) + 1)} := fun n =>
    measurableSet_lt measurable_const ((hχ.abs.div_const _).measurable.comp (hZ n))
  obtain ⟨R, hR, htail⟩ := htight δ hδ
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (hsub R hR ε hε)] with n hn
  refine (measure_mono ?_).trans (htail n)
  intro ω hω
  change R < euclideanNorm (Z n ω) / ((n : ℝ) + 1)
  by_contra houtside
  have hscale : 0 < (n : ℝ) + 1 := by positivity
  have hx : euclideanNorm (Z n ω) ≤ ((n : ℝ) + 1) * R := by
    simpa only [mul_comm] using (div_le_iff₀ hscale).mp (le_of_not_gt houtside)
  exact (not_lt_of_ge (hn (Z n ω) hx)) hω

/-- Uniform spatial sublinearity controls the whole corrector path up to a
fixed time whenever a tight random bound controls the rescaled path. -/
@[nolint unusedArguments]
theorem corrector_uniform_path_remainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (χ : Vec d → ℝ)
    (Z : ℕ → Ω → Path d) (B : ℕ → Ω → ℝ) (T : ℝ≥0)
    (hsub : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x, euclideanNorm x ≤ ((n : ℝ) + 1) * R → |χ x| / ((n : ℝ) + 1) ≤ ε)
    (hbound : ∀ n ω t, t ≤ T → euclideanNorm (Z n ω t) ≤ ((n : ℝ) + 1) * B n ω)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | R < B n ω} ≤ ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n in atTop,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧ ε < |χ (Z n ω t)| / ((n : ℝ) + 1)} ≤
        ENNReal.ofReal δ := by
  intro ε δ hε hδ
  obtain ⟨R, hR, htail⟩ := htight δ hδ
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (hsub R hR ε hε)] with n hn
  refine (measure_mono ?_).trans (htail n)
  rintro ω ⟨t, ht, hω⟩
  change R < B n ω
  by_contra houtside
  have hscale : 0 ≤ (n : ℝ) + 1 := by positivity
  have hx : euclideanNorm (Z n ω t) ≤ ((n : ℝ) + 1) * R :=
    (hbound n ω t ht).trans (mul_le_mul_of_nonneg_left (le_of_not_gt houtside) hscale)
  exact (not_lt_of_ge (hn (Z n ω t) hx)) hω

/-- Uniform sublinearity at natural radii controls every fixed multiple of a
real radius, with the same explicit Euclidean norm. -/
theorem real_scale_uniform_sublinearity_of_nat_scale {d : ℕ} (χ : Vec d → ℝ)
    (hn : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ x, euclideanNorm x ≤ (n : ℝ) + 1 → |χ x| / ((n : ℝ) + 1) ≤ ε) :
    ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t + 1) * R → |χ x| / (t + 1) ≤ ε := by
  intro R hR ε hε
  have hR2 : 0 < R + 2 := by linarith only [hR]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hn (ε / (R + 2)) (div_pos hε hR2))
  filter_upwards [eventually_ge_atTop (N : ℝ)] with t ht
  have ht0 : 0 ≤ t := (Nat.cast_nonneg N).trans ht
  have hs : 0 < t + 1 := by linarith only [ht0]
  have hrad : 0 ≤ (t + 1) * (R + 1) := by positivity
  let n : ℕ := ⌊(t + 1) * (R + 1)⌋₊
  have hnN : N ≤ n := Nat.le_floor (calc
    (N : ℝ) ≤ t := ht
    _ ≤ t + 1 := le_add_of_nonneg_right zero_le_one
    _ ≤ (t + 1) * (R + 1) :=
      le_mul_of_one_le_right hs.le (by linarith only [hR]))
  have hcover : (t + 1) * R ≤ (n : ℝ) + 1 := by
    have hf := Nat.lt_floor_add_one ((t + 1) * (R + 1))
    change (t + 1) * (R + 1) < (n : ℝ) + 1 at hf
    nlinarith only [hf, hs]
  have hupper : (n : ℝ) + 1 ≤ (t + 1) * (R + 2) := by
    have hf : (n : ℝ) ≤ (t + 1) * (R + 1) := Nat.floor_le hrad
    nlinarith only [hf, ht0]
  intro x hx
  have hsmall := (div_le_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mp
    (hN n hnN x (hx.trans hcover))
  apply (div_le_iff₀ hs).2
  calc
    |χ x| ≤ ε / (R + 2) * ((n : ℝ) + 1) := hsmall
    _ ≤ ε / (R + 2) * ((t + 1) * (R + 2)) :=
      mul_le_mul_of_nonneg_left hupper (div_pos hε hR2).le
    _ = ε * (t + 1) := by
      rw [mul_comm (t + 1) (R + 2), ← mul_assoc, div_mul_cancel₀ _ hR2.ne']

/-- Vanishing mean-subtracted spatial energy and a uniform Hölder estimate
give uniform smallness when each function is anchored at the origin. -/
theorem anchored_holder_oscillation_implies_uniform_small {d : ℕ} (hd : 1 ≤ d)
    (f : ℕ → Vec d → ℝ) (α C : ℝ) (hα : 0 < α) (hC : 0 ≤ C)
    (hmem : ∀ n, MemLp (f n) 2 (volume.restrict (ball (0 : Vec d) 1)))
    (hzero : ∀ n, f n 0 = 0)
    (hholder : ∀ n x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
      |f n x - f n y| ≤ C * euclideanNorm (x-y)^α)
    (hosc : Tendsto (fun n => ∫ x in ball (0 : Vec d) 1,
      (f n x - ⨍ y in ball (0 : Vec d) 1, f n y ∂volume)^2 ∂volume) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x,
      euclideanNorm x ≤ 1/2 → |f n x| ≤ ε := by
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp
        (Correctors.ball_volume_pos_finite d 1 zero_lt_one)).2.ne
  let g : ℕ → Vec d → ℝ := fun n x =>
    f n x - ⨍ y in ball (0 : Vec d) 1, f n y ∂volume
  have hgmem : ∀ n, MemLp (g n) 2 (volume.restrict (ball (0 : Vec d) 1)) :=
    fun n => (hmem n).sub (memLp_const _)
  have hgholder : ∀ n x y, euclideanNorm x < 1 → euclideanNorm y < 1 →
      |g n x - g n y| ≤ C * euclideanNorm (x-y)^α := by
    intro n x y hx hy
    simpa only [g, sub_sub_sub_cancel_right] using hholder n x y hx hy
  have hgsmall := holder_l2_small_implies_uniform_small hd g α C hα hC
    hgmem hgholder hosc
  intro ε hε
  filter_upwards [hgsmall (ε / 2) (half_pos hε)] with n hn
  intro x hx
  have h0 : euclideanNorm (0 : Vec d) ≤ 1/2 := by
    simp only [euclideanNorm, euclideanSq, dot, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, Real.sqrt_zero]
    norm_num
  have hidentity : f n x = g n x - g n 0 := by
    dsimp [g]
    rw [hzero n]
    ring
  calc
    |f n x| = |g n x - g n 0| := congrArg abs hidentity
    _ ≤ |g n x| + |g n 0| := abs_sub _ _
    _ ≤ ε := by linarith only [hn x hx, hn 0 h0]

/-- Global sublinear corrector growth bounds every path in a harmonic-coordinate
decomposition, with one constant chosen before the two paths. -/
theorem harmonic_coordinate_growth_absorption {d : ℕ} (χ : Vec d → Vec d)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, euclideanNorm (χ x) ≤ C + ε * euclideanNorm x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X M : Path d,
      (∀ t, X t + χ (X t) = M t) →
      ∀ t, euclideanNorm (X t) ≤ 2 * euclideanNorm (M t) + C := by
  obtain ⟨C, hC, hbound⟩ := hsub (1 / 2) (by norm_num)
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro X M hcoord t
  have hrepr : X t = M t + -χ (X t) := by
    rw [← hcoord t, add_neg_cancel_right]
  have hneg : euclideanNorm (-χ (X t)) = euclideanNorm (χ (X t)) := by
    simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
      TimeChange.euclideanNorm_smul (-1) (χ (X t))
  have htriangle := TimeChange.euclideanNorm_add_le (M t) (-χ (X t))
  rw [← hrepr, hneg] at htriangle
  linarith only [htriangle, hbound (X t)]

/-- Under a given probability law, an almost-sure harmonic-coordinate identity
transfers uniform compact-time norm tails from the harmonic paths to the paths. -/
@[nolint unusedArguments]
theorem harmonic_coordinate_uniform_path_tightness {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (χ : Vec d → Vec d)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, euclideanNorm (χ x) ≤ C + ε * euclideanNorm x)
    (X M : ℕ → Ω → Path d) (T : ℝ≥0)
    (hcoord : ∀ n, ∀ᵐ ω ∂μ, ∀ t, X n ω t + χ (X n ω t) = M n ω t)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        R < euclideanNorm (M n ω t) / ((n : ℝ) + 1)} ≤ ENNReal.ofReal δ) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | ∃ t : ℝ≥0, t ≤ T ∧
        R < euclideanNorm (X n ω t) / ((n : ℝ) + 1)} ≤ ENNReal.ofReal δ := by
  obtain ⟨C, hC, hbound⟩ := harmonic_coordinate_growth_absorption χ hsub
  intro δ hδ
  obtain ⟨R, hR, htail⟩ := htight δ hδ
  refine ⟨2 * R + C, by positivity, ?_⟩
  intro n
  apply le_trans (measure_mono_ae ?_) (htail n)
  filter_upwards [hcoord n] with ω hω
  rintro ⟨t, ht, hx⟩
  refine ⟨t, ht, ?_⟩
  have hs : 0 < (n : ℝ) + 1 := by positivity
  have hCscale : C ≤ C * ((n : ℝ) + 1) :=
    le_mul_of_one_le_right hC (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hxlarge := (lt_div_iff₀ hs).mp hx
  have habsorb := hbound (X n ω) (M n ω) hω t
  apply (lt_div_iff₀ hs).2
  linarith only [hxlarge, habsorb, hCscale]

/-- Sublinear corrector growth and tight harmonic-coordinate paths make the
whole compact-time corrector remainder vanish in probability. -/
theorem harmonic_corrector_uniform_path_remainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (χ : Vec d → Vec d)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, euclideanNorm (χ x) ≤ C + ε * euclideanNorm x)
    (X M : ℕ → Ω → Path d) (T : ℝ≥0)
    (hcoord : ∀ n, ∀ᵐ ω ∂μ, ∀ s, X n ω s + χ (X n ω s) = M n ω s)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | ∃ s : ℝ≥0, s ≤ T ∧
        R < euclideanNorm (M n ω s) / ((n : ℝ) + 1)} ≤ ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ s : ℝ≥0, s ≤ T ∧
        ε < euclideanNorm (χ (X n ω s)) / ((n : ℝ) + 1)} ≤ ENNReal.ofReal δ := by
  intro ε δ hε hδ
  obtain ⟨R, hR, htail⟩ :=
    harmonic_coordinate_uniform_path_tightness μ χ hsub X M T hcoord htight δ hδ
  have hslope : 0 < (ε / 2) / R := div_pos (half_pos hε) hR
  obtain ⟨C, _hC, hbound⟩ := hsub ((ε / 2) / R) hslope
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (C / (ε / 2)))] with n hn
  refine (measure_mono ?_).trans (htail n)
  rintro ω ⟨s, hs, hbad⟩
  refine ⟨s, hs, ?_⟩
  by_contra houtside
  have hscale : 0 < (n : ℝ) + 1 := by positivity
  have hx : euclideanNorm (X n ω s) ≤ R * ((n : ℝ) + 1) :=
    (div_le_iff₀ hscale).mp (le_of_not_gt houtside)
  have hconstant : C ≤ (ε / 2) * ((n : ℝ) + 1) := by
    have hCn := (div_le_iff₀ (half_pos hε)).mp hn
    linarith only [hCn, hε]
  have hlinear : ((ε / 2) / R) * euclideanNorm (X n ω s) ≤
      (ε / 2) * ((n : ℝ) + 1) := calc
    _ ≤ ((ε / 2) / R) * (R * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hx hslope.le
    _ = (ε / 2) * ((n : ℝ) + 1) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hR.ne']
  have hsmall : euclideanNorm (χ (X n ω s)) / ((n : ℝ) + 1) ≤ ε := by
    apply (div_le_iff₀ hscale).2
    linarith only [hbound (X n ω s), hconstant, hlinear]
  exact (not_lt_of_ge hsmall) hbad

/-- Componentwise uniform sublinearity gives arbitrarily small global linear
Euclidean growth, with one additive constant chosen before the point. -/
theorem euclidean_growth_of_component_sublinearity {d : ℕ}
    (χ : Vec d → Vec d)
    (hsub : ∀ i : Fin d, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ x, euclideanNorm x ≤ (n : ℝ) + 1 → |χ x i| / ((n : ℝ) + 1) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, euclideanNorm (χ x) ≤ C + ε * euclideanNorm x := by
  intro ε hε
  have hD : 0 < (d : ℝ) + 1 := by positivity
  have hδ : 0 < ε / ((d : ℝ) + 1) := div_pos hε hD
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_all.2 fun i => hsub i (ε / ((d : ℝ) + 1)) hδ)
  refine ⟨ε * ((N : ℝ) + 1), by positivity, ?_⟩
  intro x
  let n : ℕ := N + ⌊euclideanNorm x⌋₊
  have hnN : N ≤ n := Nat.le_add_right _ _
  have hcover : euclideanNorm x ≤ (n : ℝ) + 1 := by
    have hf := Nat.lt_floor_add_one (euclideanNorm x)
    dsimp [n]
    rw [Nat.cast_add]
    linarith only [hf, Nat.cast_nonneg (α := ℝ) N]
  have hupper : (n : ℝ) + 1 ≤ ((N : ℝ) + 1) + euclideanNorm x := by
    have hf : (⌊euclideanNorm x⌋₊ : ℝ) ≤ euclideanNorm x :=
      Nat.floor_le (Real.sqrt_nonneg (euclideanSq x))
    dsimp [n]
    rw [Nat.cast_add]
    linarith only [hf]
  have hpi : ‖χ x‖ ≤ ε / ((d : ℝ) + 1) * ((n : ℝ) + 1) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [Real.norm_eq_abs]
    exact (div_le_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mp
      (hN n hnN i x hcover)
  calc
    euclideanNorm (χ x) ≤ ((d : ℝ) + 1) * ‖χ x‖ :=
      euclideanNorm_le_dimension_mul_norm (χ x)
    _ ≤ ((d : ℝ) + 1) * (ε / ((d : ℝ) + 1) * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hpi hD.le
    _ = ε * ((n : ℝ) + 1) := by
      rw [← mul_assoc, mul_div_cancel₀ _ hD.ne']
    _ ≤ ε * (((N : ℝ) + 1) + euclideanNorm x) :=
      mul_le_mul_of_nonneg_left hupper hε.le
    _ = ε * ((N : ℝ) + 1) + ε * euclideanNorm x := mul_add _ _ _

/-- Componentwise spatial sublinearity and tight harmonic-coordinate paths give
a corrector remainder vanishing uniformly on compact time intervals in probability. -/
theorem harmonic_path_remainder_of_component_sublinearity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (χ : Vec d → Vec d)
    (hsub : ∀ i : Fin d, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ x, euclideanNorm x ≤ (n:ℝ)+1 → |χ x i| / ((n:ℝ)+1) ≤ ε)
    (X M : ℕ → Ω → Path d) (T : ℝ≥0)
    (hcoord : ∀ n, ∀ᵐ ω ∂μ, ∀ s, X n ω s + χ (X n ω s) = M n ω s)
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ n,
      μ {ω | ∃ s : ℝ≥0, s ≤ T ∧
        R < euclideanNorm (M n ω s) / ((n : ℝ) + 1)} ≤ ENNReal.ofReal δ) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      μ {ω | ∃ s : ℝ≥0, s ≤ T ∧
        ε < euclideanNorm (χ (X n ω s)) / ((n : ℝ) + 1)} ≤ ENNReal.ofReal δ := by
  exact harmonic_corrector_uniform_path_remainder μ χ
    (euclidean_growth_of_component_sublinearity χ hsub) X M T hcoord htight

end EinsteinFull
