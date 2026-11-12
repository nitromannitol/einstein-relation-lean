import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Exponential

/-! # Gamma times

Real-analysis facts about the Gamma(m+1, μ) densities `gk μ m`, used by the discrete resolvent route
to Lemma 4.1: the tails
`∫_u^∞ gk μ m = gtail μ m u`, exponential moments, and the decomposition of the exponential law of
rate `s < μ` into Gamma laws with geometric weights.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

noncomputable section

namespace EinsteinRelation.Entropy

/-- The Gamma(m+1, μ) density on `[0, ∞)`, without the indicator. -/
def gkPoly (μ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  μ ^ (m + 1) * t ^ m * Real.exp (-(μ * t)) / m.factorial

/-- The Gamma(m+1, μ) density. -/
def gk (μ : ℝ) (m : ℕ) (t : ℝ) : ℝ := if 0 ≤ t then gkPoly μ m t else 0

/-- The tail `∫_u^∞ gk μ m`, for `u ≥ 0`. -/
def gtail (μ : ℝ) (m : ℕ) (u : ℝ) : ℝ := ∑ k ∈ Finset.range (m + 1), gkPoly μ k u / μ

theorem gkPoly_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gkPoly μ m t := by
  unfold gkPoly
  positivity

theorem gk_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (m : ℕ) (t : ℝ) : 0 ≤ gk μ m t := by
  unfold gk
  split_ifs with ht
  · exact gkPoly_nonneg hμ m ht
  · exact le_rfl

theorem gk_of_nonneg (μ : ℝ) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : gk μ m t = gkPoly μ m t := if_pos ht

theorem gk_of_neg (μ : ℝ) (m : ℕ) {t : ℝ} (ht : t < 0) : gk μ m t = 0 := if_neg (not_le.mpr ht)

theorem continuous_gkPoly (μ : ℝ) (m : ℕ) : Continuous (gkPoly μ m) := by
  unfold gkPoly
  fun_prop

theorem measurable_gk (μ : ℝ) (m : ℕ) : Measurable (gk μ m) :=
  Measurable.ite measurableSet_Ici (continuous_gkPoly μ m).measurable measurable_const

theorem hasDerivAt_exp_neg_mul (μ t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(μ * t))) (Real.exp (-(μ * t)) * (-μ)) t := by
  have := ((hasDerivAt_id t).const_mul μ).neg.exp
  simpa using this

theorem hasDerivAt_gkPoly_zero (μ t : ℝ) :
    HasDerivAt (gkPoly μ 0) (-(μ * gkPoly μ 0 t)) t := by
  have e : gkPoly μ 0 = fun t => μ * Real.exp (-(μ * t)) := by
    funext t
    simp [gkPoly]
  rw [e]
  convert (hasDerivAt_exp_neg_mul μ t).const_mul μ using 1
  ring

theorem hasDerivAt_gkPoly_succ (μ : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (gkPoly μ (m + 1)) (μ * (gkPoly μ m t - gkPoly μ (m + 1) t)) t := by
  have h2 := (((hasDerivAt_pow (m + 1) t).const_mul (μ ^ (m + 1 + 1))).mul
    (hasDerivAt_exp_neg_mul μ t)).div_const ((m + 1).factorial : ℝ)
  have hf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  convert h2 using 1
  simp only [gkPoly, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem gtail_succ (μ : ℝ) (m : ℕ) :
    gtail μ (m + 1) = fun u => gtail μ m u + gkPoly μ (m + 1) u / μ := by
  funext u
  simp only [gtail, Finset.sum_range_succ]

theorem hasDerivAt_gtail {μ : ℝ} (hμ : μ ≠ 0) (m : ℕ) (t : ℝ) :
    HasDerivAt (gtail μ m) (-gkPoly μ m t) t := by
  induction m with
  | zero =>
    have e : gtail μ 0 = fun u => gkPoly μ 0 u / μ := by
      funext u
      simp [gtail]
    rw [e]
    convert (hasDerivAt_gkPoly_zero μ t).div_const μ using 1
    field_simp
  | succ m ih =>
    rw [gtail_succ]
    convert ih.add ((hasDerivAt_gkPoly_succ μ m t).div_const μ) using 1
    field_simp
    ring

theorem tendsto_gkPoly {μ : ℝ} (hμ : 0 < μ) (m : ℕ) :
    Tendsto (gkPoly μ m) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
    (tendsto_id.const_mul_atTop hμ)).const_mul (μ / m.factorial)
  rw [mul_zero] at h
  refine h.congr fun t => ?_
  simp only [Function.comp, id, gkPoly]
  ring

theorem tendsto_gtail {μ : ℝ} (hμ : 0 < μ) (m : ℕ) : Tendsto (gtail μ m) atTop (𝓝 0) := by
  have h := tendsto_finset_sum (Finset.range (m + 1)) fun k _ => (tendsto_gkPoly hμ k).div_const μ
  simp only [zero_div, Finset.sum_const_zero] at h
  exact h

theorem gtail_zero {μ : ℝ} (hμ : μ ≠ 0) (m : ℕ) : gtail μ m 0 = 1 := by
  induction m with
  | zero => simp [gtail, gkPoly, hμ]
  | succ m ih => simp [gtail_succ, ih, gkPoly]

theorem gtail_nonneg {μ : ℝ} (hμ : 0 < μ) (m : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ gtail μ m u :=
  Finset.sum_nonneg fun k _ => div_nonneg (gkPoly_nonneg hμ.le k hu) hμ.le

theorem integral_Ioi_gkPoly {μ : ℝ} (hμ : 0 < μ) (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ∫ t in Ioi u, gkPoly μ m t = gtail μ m u := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun u => -gtail μ m u) (l := 0)
    (hasDerivAt_gtail hμ.ne' m u).neg.continuousAt.continuousWithinAt
    (fun x _ => by simpa using (hasDerivAt_gtail hμ.ne' m x).neg)
    (fun x hx => gkPoly_nonneg hμ.le m (hu.trans (le_of_lt hx)))
    (by simpa using (tendsto_gtail hμ m).neg)
  simpa using h

theorem integrableOn_Ioi_gkPoly {μ : ℝ} (hμ : 0 < μ) (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn (gkPoly μ m) (Ioi u) :=
  integrableOn_Ioi_deriv_of_nonneg (g := fun u => -gtail μ m u) (l := 0)
    (hasDerivAt_gtail hμ.ne' m u).neg.continuousAt.continuousWithinAt
    (fun x _ => by simpa using (hasDerivAt_gtail hμ.ne' m x).neg)
    (fun x hx => gkPoly_nonneg hμ.le m (hu.trans (le_of_lt hx)))
    (by simpa using (tendsto_gtail hμ m).neg)

/-! ## Moments -/

theorem gkPoly_mul_exp {μ c : ℝ} (hμc : c < μ) (m : ℕ) (t : ℝ) :
    gkPoly μ m t * Real.exp (c * t) = (μ / (μ - c)) ^ (m + 1) * gkPoly (μ - c) m t := by
  have hμc' : μ - c ≠ 0 := (sub_pos.mpr hμc).ne'
  have h1 : Real.exp (-(μ * t)) * Real.exp (c * t) = Real.exp (-((μ - c) * t)) := by
    rw [← Real.exp_add]
    ring_nf
  unfold gkPoly
  rw [show μ ^ (m + 1) * t ^ m * Real.exp (-(μ * t)) / m.factorial * Real.exp (c * t) =
      μ ^ (m + 1) * t ^ m * (Real.exp (-(μ * t)) * Real.exp (c * t)) / m.factorial by ring, h1,
    div_pow]
  field_simp

theorem integral_Ioi_gkPoly_mul_exp {μ c : ℝ} (hμc : c < μ) (m : ℕ) :
    ∫ t in Ioi 0, gkPoly μ m t * Real.exp (c * t) = (μ / (μ - c)) ^ (m + 1) := by
  rw [integral_congr_ae (ae_of_all _ (gkPoly_mul_exp hμc m)), integral_const_mul,
    integral_Ioi_gkPoly (sub_pos.mpr hμc) m le_rfl, gtail_zero (sub_pos.mpr hμc).ne', mul_one]

theorem integrableOn_Ioi_gkPoly_mul_exp {μ c : ℝ} (hμc : c < μ) (m : ℕ) :
    IntegrableOn (fun t => gkPoly μ m t * Real.exp (c * t)) (Ioi 0) := by
  have h : IntegrableOn (fun t => (μ / (μ - c)) ^ (m + 1) * gkPoly (μ - c) m t) (Ioi 0) :=
    (integrableOn_Ioi_gkPoly (sub_pos.mpr hμc) m le_rfl).const_mul _
  exact IntegrableOn.congr_fun h (fun t _ => (gkPoly_mul_exp hμc m t).symm) measurableSet_Ioi

theorem mul_gkPoly {μ : ℝ} (hμ : μ ≠ 0) (m : ℕ) (t : ℝ) :
    t * gkPoly μ m t = ((m : ℝ) + 1) / μ * gkPoly μ (m + 1) t := by
  have hf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  unfold gkPoly
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem gk_eq_indicator (μ : ℝ) (m : ℕ) : gk μ m = (Ici 0).indicator (gkPoly μ m) := by
  funext t
  simp only [gk, Set.indicator_apply, Set.mem_Ici]

theorem integrable_gk {μ : ℝ} (hμ : 0 < μ) (m : ℕ) : Integrable (gk μ m) := by
  rw [gk_eq_indicator, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_Ioi_gkPoly hμ m le_rfl

theorem integral_gk_mul (μ : ℝ) (m : ℕ) (g : ℝ → ℝ) :
    ∫ t, gk μ m t * g t = ∫ t in Ioi 0, gkPoly μ m t * g t := by
  have e : (fun t => gk μ m t * g t) = (Ici 0).indicator (fun t => gkPoly μ m t * g t) := by
    funext t
    simp only [gk, Set.indicator_apply, Set.mem_Ici]
    split_ifs <;> simp
  rw [e, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem integral_gk {μ : ℝ} (hμ : 0 < μ) (m : ℕ) : ∫ t, gk μ m t = 1 := by
  have h := integral_gk_mul μ m (fun _ => 1)
  simp only [mul_one] at h
  rw [h, integral_Ioi_gkPoly hμ m le_rfl, gtail_zero hμ.ne']

theorem integrable_mul_gk {μ : ℝ} (hμ : 0 < μ) (m : ℕ) : Integrable (fun t => t * gk μ m t) := by
  have e : (fun t => t * gk μ m t) = fun t => ((m : ℝ) + 1) / μ * gk μ (m + 1) t := by
    funext t
    simp only [gk]
    split_ifs
    · exact mul_gkPoly hμ.ne' m t
    · simp
  rw [e]
  exact (integrable_gk hμ (m + 1)).const_mul _

theorem gk_mul_exp_eq_indicator (μ c : ℝ) (m : ℕ) :
    (fun t => gk μ m t * Real.exp (c * t)) =
      (Ici 0).indicator (fun t => gkPoly μ m t * Real.exp (c * t)) := by
  funext t
  simp only [gk, Set.indicator_apply, Set.mem_Ici]
  split_ifs <;> simp

theorem integrable_gk_mul_exp {μ c : ℝ} (hμc : c < μ) (m : ℕ) :
    Integrable (fun t => gk μ m t * Real.exp (c * t)) := by
  rw [gk_mul_exp_eq_indicator, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_Ioi_gkPoly_mul_exp hμc m

theorem integral_gk_mul_exp {μ c : ℝ} (hμc : c < μ) (m : ℕ) :
    ∫ t, gk μ m t * Real.exp (c * t) = (μ / (μ - c)) ^ (m + 1) := by
  rw [integral_gk_mul, integral_Ioi_gkPoly_mul_exp hμc m]

/-! ## The exponential law as a mixture of Gamma laws -/

/-- The geometric weights `w_m = (s/μ)(1 - s/μ)^m`. -/
def gweight (s μ : ℝ) (m : ℕ) : ℝ := s / μ * (1 - s / μ) ^ m

theorem gweight_nonneg {s μ : ℝ} (hs : 0 ≤ s) (hsμ : s ≤ μ) (hμ : 0 < μ) (m : ℕ) :
    0 ≤ gweight s μ m := by
  have : s / μ ≤ 1 := (div_le_one hμ).mpr hsμ
  unfold gweight
  exact mul_nonneg (div_nonneg hs hμ.le) (pow_nonneg (by linarith) m)

theorem gweight_mul_gkPoly {s μ : ℝ} (hμ : μ ≠ 0) (m : ℕ) (t : ℝ) :
    gweight s μ m * gkPoly μ m t =
      s * Real.exp (-(μ * t)) * (((μ - s) * t) ^ m / m.factorial) := by
  have hf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  unfold gweight gkPoly
  rw [one_sub_div hμ, div_pow, mul_pow, pow_succ]
  field_simp

theorem hasSum_gweight_mul_gkPoly {s μ : ℝ} (hμ : μ ≠ 0) (t : ℝ) :
    HasSum (fun m => gweight s μ m * gkPoly μ m t) (s * Real.exp (-(s * t))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ℝ ((μ - s) * t)).mul_left
    (s * Real.exp (-(μ * t)))
  rw [← Real.exp_eq_exp_ℝ, mul_assoc, ← Real.exp_add] at h
  convert h using 1
  · funext m
    exact gweight_mul_gkPoly hμ m t
  · ring_nf

/-- The exponential density of rate `s` is the `gweight`-mixture of the Gamma densities of rate
`μ`, for `0 < s ≤ μ`. -/
theorem exponentialPDF_eq_tsum {s μ : ℝ} (hs : 0 < s) (hsμ : s ≤ μ) (t : ℝ) :
    ProbabilityTheory.exponentialPDF s t =
      ∑' m, ENNReal.ofReal (gweight s μ m * gk μ m t) := by
  have hμ : 0 < μ := hs.trans_le hsμ
  rw [ProbabilityTheory.exponentialPDF_eq]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    simp only [gk_of_nonneg μ _ ht]
    have hsum := hasSum_gweight_mul_gkPoly (s := s) hμ.ne' t
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m =>
      mul_nonneg (gweight_nonneg hs.le hsμ hμ m) (gkPoly_nonneg hμ.le m ht)) hsum.summable]
  · rw [if_neg ht]
    simp [gk_of_neg μ _ (not_le.mp ht)]

/-! ## Gamma averages of time integrals -/

/-- **Gamma averages of time integrals**: `∫ gk_m(t) ∫_0^t h = μ⁻¹ ∑_{k ≤ m} ∫ gk_k h` for bounded
measurable `h`. -/
theorem integral_gk_mul_intervalIntegral {μ : ℝ} (hμ : 0 < μ) (m : ℕ) {h : ℝ → ℝ}
    (hm : Measurable h) {B : ℝ} (hB : ∀ u, |h u| ≤ B) :
    ∫ t, gk μ m t * (∫ u in (0 : ℝ)..t, h u) =
      ∑ k ∈ Finset.range (m + 1), (∫ u, gk μ k u * h u) / μ := by
  set S : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ p.1} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  set F : ℝ → ℝ → ℝ := fun t u => gk μ m t * S.indicator (fun p => h p.2) (t, u) with hFdef
  have hSind : ∀ t u, S.indicator (fun p : ℝ × ℝ => h p.2) (t, u) = (Ioc 0 t).indicator h u :=
    fun t u => by simp only [Set.indicator_apply, hSdef, Set.mem_setOf_eq, Set.mem_Ioc]
  have hF : ∀ t u, F t u = gk μ m t * (Ioc 0 t).indicator h u := fun t u => by
    simp only [hFdef, hSind]
  -- The inner integrals in `u`.
  have h1 : ∀ t, ∫ u, F t u = gk μ m t * ∫ u in (0 : ℝ)..t, h u := fun t => by
    simp only [hF]
    rw [integral_const_mul]
    by_cases ht : 0 ≤ t
    · rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le ht]
    · rw [gk_of_neg μ m (not_le.mp ht), zero_mul, zero_mul]
  -- The inner integrals in `t`.
  have h2 : ∀ u, ∫ t, F t u = (Ioi 0).indicator (fun u => h u * gtail μ m u) u := fun u => by
    simp only [hF]
    by_cases hu : 0 < u
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hu)]
      have e : ∀ t, gk μ m t * (Ioc 0 t).indicator h u =
          (Ici u).indicator (fun t => h u * gkPoly μ m t) t := fun t => by
        by_cases htu : u ≤ t
        · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu, htu⟩),
            Set.indicator_of_mem (Set.mem_Ici.mpr htu), gk_of_nonneg μ m (hu.le.trans htu),
            mul_comm]
        · rw [Set.indicator_of_notMem (fun h' => htu (Set.mem_Ioc.mp h').2),
            Set.indicator_of_notMem (fun h' => htu (Set.mem_Ici.mp h')), mul_zero]
      rw [integral_congr_ae (ae_of_all _ e), integral_indicator measurableSet_Ici,
        integral_Ici_eq_integral_Ioi, integral_const_mul, integral_Ioi_gkPoly hμ m hu.le]
    · rw [Set.indicator_of_notMem (s := Ioi 0) (by simpa using hu)]
      have e : ∀ t, gk μ m t * (Ioc 0 t).indicator h u = 0 := fun t => by
        rw [Set.indicator_of_notMem (fun h' => hu (Set.mem_Ioc.mp h').1), mul_zero]
      simp only [e, integral_zero]
  -- Integrability on the product.
  have hFu : Function.uncurry F = fun p => gk μ m p.1 * S.indicator (fun q => h q.2) p := by
    funext p
    rfl
  have hFm : Measurable (Function.uncurry F) := by
    rw [hFu]
    exact ((measurable_gk μ m).comp measurable_fst).mul ((hm.comp measurable_snd).indicator hS)
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun t => ?_, ?_⟩
    · have hi : Integrable ((Ioc 0 t).indicator h) := by
        rw [integrable_indicator_iff measurableSet_Ioc]
        exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable
          (ae_of_all _ fun u => (Real.norm_eq_abs _).trans_le (hB u))
      simpa only [Function.uncurry_apply_pair, hF] using hi.const_mul (gk μ m t)
    · refine Integrable.mono' ((integrable_mul_gk hμ m).const_mul B)
        hFm.aestronglyMeasurable.norm.integral_prod_right' (ae_of_all _ fun t => ?_)
      simp only [Function.uncurry_apply_pair, hF, norm_mul, Real.norm_eq_abs]
      rw [integral_const_mul, abs_of_nonneg (gk_nonneg hμ.le m t)]
      have hn : 0 ≤ ∫ u, |(Ioc 0 t).indicator h u| := integral_nonneg fun u => abs_nonneg _
      rw [abs_of_nonneg (mul_nonneg (gk_nonneg hμ.le m t) hn)]
      by_cases ht : 0 ≤ t
      · have e : (fun u => |(Ioc 0 t).indicator h u|) = (Ioc 0 t).indicator (fun u => |h u|) := by
          funext u
          simp only [Set.indicator_apply]
          split_ifs <;> simp
        rw [e, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le ht]
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
          (f := fun u => |h u|) (C := B) fun u _ => by
            rw [Real.norm_eq_abs, abs_abs]
            exact hB u
        rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at hb
        calc gk μ m t * ∫ u in (0 : ℝ)..t, |h u|
            ≤ gk μ m t * (B * t) :=
              mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) (gk_nonneg hμ.le m t)
          _ = B * (t * gk μ m t) := by ring
      · rw [gk_of_neg μ m (not_le.mp ht)]
        simp
  -- Swap and evaluate.
  have hswap := integral_integral_swap hFi
  simp only [h1, h2] at hswap
  rw [hswap, integral_indicator measurableSet_Ioi]
  have hint : ∀ k ∈ Finset.range (m + 1), IntegrableOn (fun u => h u * (gkPoly μ k u / μ)) (Ioi 0) :=
    fun k _ => by
      have hk : IntegrableOn (gkPoly μ k) (Ioi 0) := integrableOn_Ioi_gkPoly hμ k le_rfl
      refine Integrable.mono' (hk.div_const μ |>.const_mul B)
        (hm.aestronglyMeasurable.mul (hk.div_const μ).aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (gkPoly_nonneg hμ.le k
        (le_of_lt hu)) hμ.le)]
      exact mul_le_mul_of_nonneg_right (hB u) (div_nonneg (gkPoly_nonneg hμ.le k (le_of_lt hu)) hμ.le)
  simp only [gtail, Finset.mul_sum]
  rw [integral_finset_sum _ hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_gk_mul, ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  ring

end EinsteinRelation.Entropy
