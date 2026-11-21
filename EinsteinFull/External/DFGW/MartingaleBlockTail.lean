import EinsteinFull.External.DFGW.MartingaleTailMaximal
import EinsteinFull.External.DFGW.Trajectory
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Block oscillations of stationary-increment martingales

At diffusive scale, the oscillation of a stationary-increment martingale over the `2 ^ a` blocks
of a long interval is controlled, uniformly in the length of the interval, once `a` is large.
The estimate combines a union bound over blocks, stationarity, Doob's inequality on the event of
a large terminal value, and uniform integrability of the normalized squared terminal values, which
follows from convergence of their truncated means and of their means (Billingsley, *Convergence
of Probability Measures*, Theorem 3.6), here with a comparison process converging in law.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

section Truncation

/-- Convergence of means and of truncated means gives convergence of the means above any
level. -/
theorem tendsto_integral_max_sub_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ν : Measure ℝ} [IsFiniteMeasure ν] (Q : ℕ → Ω → ℝ) (hQ : ∀ n, Integrable (Q n) P)
    [IsFiniteMeasure P] {s Λ : ℝ} (hν : Integrable (fun x => x ^ 2) ν)
    (hνs : ∫ x, x ^ 2 ∂ν = s)
    (hmean : Tendsto (fun n => ∫ ω, Q n ω ∂P) atTop (𝓝 s))
    (hmin : Tendsto (fun n => ∫ ω, min (Q n ω) Λ ∂P) atTop (𝓝 (∫ x, min (x ^ 2) Λ ∂ν))) :
    Tendsto (fun n => ∫ ω, max (Q n ω - Λ) 0 ∂P) atTop
      (𝓝 (∫ x, max (x ^ 2 - Λ) 0 ∂ν)) := by
  have hid (y : ℝ) : max (y - Λ) 0 = y - min y Λ := by
    rcases le_total y Λ with h | h
    · rw [max_eq_right (by linarith), min_eq_left h]
      ring
    · rw [max_eq_left (by linarith), min_eq_right h]
  have hQmin (n : ℕ) : Integrable (fun ω => min (Q n ω) Λ) P :=
    (hQ n).inf (integrable_const Λ)
  have hνmin : Integrable (fun x : ℝ => min (x ^ 2) Λ) ν := hν.inf (integrable_const Λ)
  have hleft (n : ℕ) : (∫ ω, max (Q n ω - Λ) 0 ∂P) =
      (∫ ω, Q n ω ∂P) - ∫ ω, min (Q n ω) Λ ∂P := by
    simp_rw [hid]
    exact integral_sub (hQ n) (hQmin n)
  have hright : (∫ x, max (x ^ 2 - Λ) 0 ∂ν) = s - ∫ x, min (x ^ 2) Λ ∂ν := by
    simp_rw [hid]
    rw [integral_sub hν hνmin, hνs]
  simp_rw [hleft]
  rw [hright]
  exact hmean.sub hmin

/-- The mean of a square-integrable law above a level tends to zero as the level grows. -/
theorem tendsto_integral_max_sq_sub_atTop {ν : Measure ℝ} (hν : Integrable (fun x => x ^ 2) ν) :
    Tendsto (fun Λ : ℝ => ∫ x, max (x ^ 2 - Λ) 0 ∂ν) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := atTop)
    (F := fun (Λ : ℝ) (x : ℝ) => max (x ^ 2 - Λ) 0) (f := fun _ => (0 : ℝ))
    (fun x => x ^ 2)
    (Eventually.of_forall fun Λ => (by fun_prop : Continuous fun x : ℝ =>
      max (x ^ 2 - Λ) 0).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with Λ hΛ
      refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith) (sq_nonneg x))
    hν
    (ae_of_all _ fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (x ^ 2)] with Λ hΛ
      rw [max_eq_right (by linarith)])
  simpa only [integral_zero] using h

/-- A large terminal value of `f` forces a large truncated square of a comparison `g` or a large
square distance between them. -/
theorem setIntegral_sq_le_of_comparison {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (f g : Ω → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) {b : ℝ}
    (hb : 0 ≤ b) :
    (∫ ω in {ω | b / 2 ≤ |f ω|}, f ω ^ 2 ∂P) ≤
      4 * (∫ ω, max (g ω ^ 2 - b ^ 2 / 16) 0 ∂P) + 4 * ∫ ω, (g ω - f ω) ^ 2 ∂P := by
  have hg2 : Integrable (fun ω => g ω ^ 2) P := hg.integrable_sq
  have hmax : Integrable (fun ω => max (g ω ^ 2 - b ^ 2 / 16) 0) P := by
    have h := (hg2.sub (integrable_const (b ^ 2 / 16))).sup (integrable_const 0)
    exact h
  have hdiff : Integrable (fun ω => (g ω - f ω) ^ 2) P := (hg.sub hf).integrable_sq
  have hf2 : Integrable (fun ω => f ω ^ 2) P := hf.integrable_sq
  have hrhs : Integrable (fun ω => 4 * max (g ω ^ 2 - b ^ 2 / 16) 0 + 4 * (g ω - f ω) ^ 2) P :=
    (hmax.const_mul 4).add (hdiff.const_mul 4)
  calc
    (∫ ω in {ω | b / 2 ≤ |f ω|}, f ω ^ 2 ∂P) ≤
        ∫ ω in {ω | b / 2 ≤ |f ω|},
          (4 * max (g ω ^ 2 - b ^ 2 / 16) 0 + 4 * (g ω - f ω) ^ 2) ∂P := by
      refine setIntegral_mono_on₀ hf2.integrableOn hrhs.integrableOn ?_ ?_
      · exact nullMeasurableSet_le aemeasurable_const
          (continuous_abs.measurable.comp_aemeasurable hf.aestronglyMeasurable.aemeasurable)
      · intro ω hω
        have h1 : b / 2 ≤ |f ω| := hω
        have h2 : b ^ 2 / 4 ≤ f ω ^ 2 := by
          have hb2 : 0 ≤ b / 2 := by positivity
          nlinarith [sq_abs (f ω), abs_nonneg (f ω), mul_le_mul h1 h1 hb2 (abs_nonneg (f ω))]
        have h3 : f ω ^ 2 ≤ 2 * g ω ^ 2 + 2 * (g ω - f ω) ^ 2 := by
          nlinarith [sq_nonneg (g ω + (g ω - f ω)), sq_nonneg (g ω - (g ω - f ω))]
        have h4 : g ω ^ 2 - b ^ 2 / 16 ≤ max (g ω ^ 2 - b ^ 2 / 16) 0 := le_max_left _ _
        nlinarith
    _ ≤ ∫ ω, (4 * max (g ω ^ 2 - b ^ 2 / 16) 0 + 4 * (g ω - f ω) ^ 2) ∂P := by
      apply setIntegral_le_integral hrhs
      exact ae_of_all _ fun ω => add_nonneg (mul_nonneg (by norm_num) (le_max_right _ _))
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = _ := by
      rw [integral_add (hmax.const_mul 4) (hdiff.const_mul 4), integral_const_mul,
        integral_const_mul]

end Truncation

section Blocks

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The block length `(n + 1) / 2 ^ a` of the `2 ^ a` blocks of `[0, n + 1]`. -/
noncomputable def blockStep (n a : ℕ) : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0) / 2 ^ a

omit [BorelSpace S] in
/-- By stationarity, the probability that some block of a stationary-increment process has a
large dyadic excursion is at most the number of blocks times the probability for the first
block. -/
theorem measureReal_shift_blocks_le (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (m : ℝ≥0 → C(ℝ, S) → ℝ) (hm : ∀ t, Measurable (m t))
    (hstat : ∀ s t, (fun η => m (s + t) η - m s η) =ᵐ[P]
      fun η => m t (Draft.dfgwShift s η)) (J : ℕ) (h : ℝ≥0) (b : ℝ) :
    P.real {η | ∃ j < J, ∃ r k, k ≤ 2 ^ r ∧
      b ≤ |m (j • h + dyadicGridTime h r k) η - m (j • h) η|} ≤
      J * P.real {η | ∃ r k, k ≤ 2 ^ r ∧ b ≤ |m (dyadicGridTime h r k) η|} := by
  let C : Set C(ℝ, S) := {η | ∃ r k, k ≤ 2 ^ r ∧ b ≤ |m (dyadicGridTime h r k) η|}
  let B : ℕ → Set C(ℝ, S) := fun j => {η | ∃ r k, k ≤ 2 ^ r ∧
    b ≤ |m (j • h + dyadicGridTime h r k) η - m (j • h) η|}
  have hCm : MeasurableSet C := by
    have hC : C = ⋃ r : ℕ, ⋃ k : ℕ,
        ({_η | k ≤ 2 ^ r} ∩ {η | b ≤ |m (dyadicGridTime h r k) η|}) := by
      ext η
      simp only [C, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [hC]
    exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun k =>
      (MeasurableSet.const _).inter
        (measurableSet_le measurable_const (continuous_abs.measurable.comp (hm _)))
  have hB (j : ℕ) : P.real (B j) = P.real C := by
    have hshift : MeasurePreserving (Draft.dfgwShift (S := S) ((j • h : ℝ≥0) : ℝ)) P P :=
      ⟨measurable_shift _, hP.stationary _⟩
    have hall : ∀ᵐ η ∂P, ∀ r k : ℕ, m (j • h + dyadicGridTime h r k) η - m (j • h) η =
        m (dyadicGridTime h r k) (Draft.dfgwShift ((j • h : ℝ≥0) : ℝ) η) := by
      rw [ae_all_iff]
      intro r
      rw [ae_all_iff]
      intro k
      exact hstat (j • h) (dyadicGridTime h r k)
    have hpre : B j =ᵐ[P] (Draft.dfgwShift ((j • h : ℝ≥0) : ℝ) ⁻¹' C : Set C(ℝ, S)) := by
      filter_upwards [hall] with η hη
      apply propext
      constructor
      · rintro ⟨r, k, hk, hb⟩
        exact ⟨r, k, hk, by rwa [hη r k] at hb⟩
      · rintro ⟨r, k, hk, hb⟩
        exact ⟨r, k, hk, by rwa [hη r k]⟩
    rw [measureReal_congr hpre, hshift.measureReal_preimage hCm.nullMeasurableSet]
  have hU : {η | ∃ j < J, ∃ r k, k ≤ 2 ^ r ∧
      b ≤ |m (j • h + dyadicGridTime h r k) η - m (j • h) η|} =
      ⋃ j ∈ Finset.range J, B j := by
    ext η
    simp only [B, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
  rw [hU]
  calc
    _ ≤ ∑ j ∈ Finset.range J, P.real (B j) := measureReal_biUnion_finset_le _ _
    _ = ∑ _j ∈ Finset.range J, P.real C := Finset.sum_congr rfl fun j _ => hB j
    _ = J * P.real C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The block length tends to infinity with the interval. -/
theorem tendsto_blockStep_atTop (a : ℕ) : Tendsto (fun n : ℕ => blockStep n a) atTop atTop := by
  have h : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  exact h.atTop_div_const (pow_pos (by norm_num) a)

/-- **Block oscillations of a stationary-increment martingale.** Let `m` be a square-integrable
martingale with stationary increments and `y` a square-integrable comparison process with
`t⁻¹ E (y t - m t) ^ 2 → 0`, whose normalized squares at the block lengths have means converging
to `σ2` and truncated means converging to those of a law `ν` with second moment `σ2`. Then for
every `c, κ > 0` there is a dyadic level `a` such that eventually the probability that some
block of `[0, n + 1]` carries a dyadic excursion of size `c √(n + 1)` is at most `κ`. -/
theorem exists_level_measureReal_martingale_blocks_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (m : ℝ≥0 → C(ℝ, S) → ℝ) (hm : Martingale m Draft.dfgwPast P)
    (hm2 : ∀ t, MemLp (m t) 2 P)
    (hstat : ∀ s t, (fun η => m (s + t) η - m s η) =ᵐ[P]
      fun η => m t (Draft.dfgwShift s η))
    (y : ℝ≥0 → C(ℝ, S) → ℝ) (hy2 : ∀ t, MemLp (y t) 2 P)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : Integrable (fun x => x ^ 2) ν) (σ2 : ℝ)
    (hνs : ∫ x, x ^ 2 ∂ν = σ2)
    (hmean : ∀ a : ℕ, Tendsto (fun n : ℕ =>
      ∫ η, y (blockStep n a) η ^ 2 / blockStep n a ∂P) atTop (𝓝 σ2))
    (hmin : ∀ (a : ℕ) (Λ : ℝ), Tendsto (fun n : ℕ =>
      ∫ η, min (y (blockStep n a) η ^ 2 / blockStep n a) Λ ∂P) atTop
        (𝓝 (∫ x, min (x ^ 2) Λ ∂ν)))
    (hrem : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ∫ η, (y t η - m t η) ^ 2 ∂P) atTop (𝓝 0))
    {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    ∃ a : ℕ, ∀ᶠ n : ℕ in atTop, P.real {η | ∃ j < 2 ^ a, ∃ r k, k ≤ 2 ^ r ∧
      c * Real.sqrt (n + 1) ≤ |m (j • blockStep n a + dyadicGridTime (blockStep n a) r k) η -
        m (j • blockStep n a) η|} ≤ κ := by
  let : IsProbabilityMeasure P := hP.probability
  have hmmeas (t : ℝ≥0) : Measurable (m t) :=
    ((hm.stronglyMeasurable t).mono (Draft.dfgwPast.le t)).measurable
  -- choice of the dyadic level
  let Λ : ℕ → ℝ := fun a => c ^ 2 * 2 ^ a / 16
  have hΛ : Tendsto Λ atTop atTop := by
    have h2 : Tendsto (fun a : ℕ => (2 : ℝ) ^ a) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h3 := (h2.const_mul_atTop (show 0 < c ^ 2 by positivity)).atTop_div_const
      (show (0 : ℝ) < 16 by norm_num)
    exact h3
  have hτ := (tendsto_integral_max_sq_sub_atTop hν).comp hΛ
  have hsmall : ∀ᶠ a : ℕ in atTop, 16 / c ^ 2 * ∫ x, max (x ^ 2 - Λ a) 0 ∂ν < κ / 2 := by
    have h := hτ.const_mul (16 / c ^ 2)
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  obtain ⟨a, ha⟩ := hsmall.exists
  refine ⟨a, ?_⟩
  -- the bound at each scale
  let h : ℕ → ℝ≥0 := fun n => blockStep n a
  have hpos (n : ℕ) : (0 : ℝ) < h n := by
    change (0 : ℝ) < ((((n + 1 : ℕ) : ℝ≥0) / 2 ^ a : ℝ≥0) : ℝ)
    rw [NNReal.coe_div]
    push_cast
    positivity
  have hhreal (n : ℕ) : ((h n : ℝ≥0) : ℝ) = ((n : ℝ) + 1) / 2 ^ a := by
    change ((((n + 1 : ℕ) : ℝ≥0) / 2 ^ a : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_div]
    push_cast
    ring
  let F : ℕ → ℝ := fun n => 16 / c ^ 2 *
    ((∫ η, max (y (h n) η ^ 2 / h n - Λ a) 0 ∂P) +
      ((h n : ℝ))⁻¹ * ∫ η, (y (h n) η - m (h n) η) ^ 2 ∂P)
  have hbound (n : ℕ) : P.real {η | ∃ j < 2 ^ a, ∃ r k, k ≤ 2 ^ r ∧
      c * Real.sqrt (n + 1) ≤ |m (j • h n + dyadicGridTime (h n) r k) η - m (j • h n) η|} ≤
      F n := by
    have hsqrt : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hb : 0 < c * Real.sqrt ((n : ℝ) + 1) := mul_pos hc hsqrt
    have hblocks := measureReal_shift_blocks_le hP m hmmeas hstat (2 ^ a) (h n)
      (c * Real.sqrt ((n : ℝ) + 1))
    have hdoob := measureReal_dyadic_martingale_max_le_tail m hm (h n) (hm2 (h n)) hb
    have hcomp := setIntegral_sq_le_of_comparison (P := P) (m (h n)) (y (h n)) (hm2 (h n))
      (hy2 (h n)) hb.le
    have hb2 : (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 = c ^ 2 * ((n : ℝ) + 1) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hmaxid : (∫ η, max (y (h n) η ^ 2 - (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 / 16) 0 ∂P) =
        (h n : ℝ) * ∫ η, max (y (h n) η ^ 2 / h n - Λ a) 0 ∂P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine ae_of_all _ fun η => ?_
      have hΛh : (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 / 16 = (h n : ℝ) * Λ a := by
        rw [hb2, hhreal]
        dsimp only [Λ]
        field_simp
      rw [hΛh]
      dsimp only
      rw [mul_max_of_nonneg _ _ (hpos n).le, mul_zero, mul_sub,
        mul_div_cancel₀ _ (hpos n).ne']
    have hdiffid : (∫ η, (y (h n) η - m (h n) η) ^ 2 ∂P) =
        (h n : ℝ) * (((h n : ℝ))⁻¹ * ∫ η, (y (h n) η - m (h n) η) ^ 2 ∂P) := by
      rw [← mul_assoc, mul_inv_cancel₀ (hpos n).ne', one_mul]
    have hcoef : (2 : ℝ) ^ a * (4 / (c * Real.sqrt ((n : ℝ) + 1)) ^ 2) * (4 * (h n : ℝ)) =
        16 / c ^ 2 := by
      rw [hb2, hhreal]
      field_simp
      ring
    have hnn1 : 0 ≤ P.real {η | ∃ r k, k ≤ 2 ^ r ∧
        c * Real.sqrt ((n : ℝ) + 1) ≤ |m (dyadicGridTime (h n) r k) η|} := measureReal_nonneg
    have hc4 : 0 ≤ 4 / (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 := by positivity
    have h2a : (0 : ℝ) ≤ 2 ^ a := by positivity
    have hpow : ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ a := by push_cast; ring
    rw [hpow] at hblocks
    calc
      _ ≤ (2 : ℝ) ^ a * P.real {η | ∃ r k, k ≤ 2 ^ r ∧
          c * Real.sqrt ((n : ℝ) + 1) ≤ |m (dyadicGridTime (h n) r k) η|} := hblocks
      _ ≤ (2 : ℝ) ^ a * (4 / (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 *
          ∫ η in {η | c * Real.sqrt ((n : ℝ) + 1) / 2 ≤ |m (h n) η|}, m (h n) η ^ 2 ∂P) :=
        mul_le_mul_of_nonneg_left hdoob h2a
      _ ≤ (2 : ℝ) ^ a * (4 / (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 *
          (4 * (∫ η, max (y (h n) η ^ 2 - (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 / 16) 0 ∂P) +
            4 * ∫ η, (y (h n) η - m (h n) η) ^ 2 ∂P)) := by
        gcongr
      _ = F n := by
        rw [hmaxid, hdiffid]
        dsimp only [F]
        rw [← hcoef]
        ring
  -- the bound converges to a limit below `κ`
  have hFlim : Tendsto F atTop (𝓝 (16 / c ^ 2 * ((∫ x, max (x ^ 2 - Λ a) 0 ∂ν) + 0))) := by
    have hQ (n : ℕ) : Integrable (fun η => y (h n) η ^ 2 / h n) P :=
      (hy2 (h n)).integrable_sq.div_const _
    have h1 := tendsto_integral_max_sub_zero (P := P) (fun n η => y (h n) η ^ 2 / h n) hQ hν hνs
      (hmean a) (hmin a (Λ a))
    have h2 := hrem.comp (tendsto_blockStep_atTop a)
    exact (h1.add h2).const_mul (16 / c ^ 2)
  have hlimlt : 16 / c ^ 2 * ((∫ x, max (x ^ 2 - Λ a) 0 ∂ν) + 0) < κ := by
    rw [add_zero]
    linarith
  filter_upwards [hFlim.eventually (gt_mem_nhds hlimlt)] with n hn
  exact (hbound n).trans hn.le

end Blocks

end EinsteinFull.External.DFGW
