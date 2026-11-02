import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Signed or absolute correlation Cesàro decay implies L¹ decay of orbit averages. -/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull.Blueprint

private lemma clock_correlation_sum_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) (n : ℕ) :
    MemLp (birkhoffSum T f n) 2 μ := by
  induction n with
  | zero => simpa only [birkhoffSum_zero] using (MemLp.zero : MemLp (0 : Ω → ℝ) 2 μ)
  | succ n ih =>
    simpa only [birkhoffSum_succ', Function.comp_def, Pi.add_apply] using
      hf.add (ih.comp_measurePreserving hT)

private lemma clock_correlation_integral_shift {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) :
    (∫ ω, g (T ω) ∂μ) = ∫ ω, g ω ∂μ := by
  have hm : AEStronglyMeasurable g (Measure.map T μ) :=
    hT.map_eq.symm ▸ hg.aestronglyMeasurable
  exact (integral_map hT.measurable.aemeasurable hm).symm.trans
    (congrArg (fun ν => ∫ ω, g ω ∂ν) hT.map_eq)

/-- The second moment of a stationary partial sum is bounded by its length
 times twice the sum of absolute lag correlations. -/
private lemma clock_correlation_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) (n : ℕ) :
    (∫ ω, (birkhoffSum T f n ω) ^ 2 ∂μ) ≤
      2 * (n : ℝ) * ∑ k ∈ Finset.range n,
        |∫ ω, f ω * f ((T^[k]) ω) ∂μ| := by
  let c : ℕ → ℝ := fun k => ∫ ω, f ω * f ((T^[k]) ω) ∂μ
  have hc0 : 0 ≤ c 0 := by
    exact integral_nonneg fun ω => mul_self_nonneg (f ω)
  have hsum (m : ℕ) := clock_correlation_sum_memLp hT hf m
  have hcross (m : ℕ) :
      (∫ ω, f ω * birkhoffSum T f m (T ω) ∂μ) =
        ∑ k ∈ Finset.range m, c (k + 1) := by
    simp only [birkhoffSum, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [c, Function.iterate_succ_apply]
    · intro k hk
      exact hf.integrable_mul (hf.comp_measurePreserving ((hT.iterate k).comp hT))
  change (∫ ω, (birkhoffSum T f n ω) ^ 2 ∂μ) ≤
    2 * (n : ℝ) * ∑ k ∈ Finset.range n, |c k|
  induction n with
  | zero => simp only [birkhoffSum_zero_apply, sq, integral_zero, Nat.cast_zero, mul_zero,
      Finset.range_zero, Finset.sum_empty, le_refl]
  | succ n ih =>
    have hshift := (hsum n).comp_measurePreserving hT
    have hprod := hf.integrable_mul hshift
    have hrec : (∫ ω, (birkhoffSum T f (n + 1) ω) ^ 2 ∂μ) =
        (∫ ω, (birkhoffSum T f n ω) ^ 2 ∂μ) +
          2 * ∑ k ∈ Finset.range n, c (k + 1) + c 0 := by
      simp_rw [birkhoffSum_succ_apply']
      have hexp : (fun ω => (f ω + birkhoffSum T f n (T ω)) ^ 2) =
          (fun ω => (birkhoffSum T f n (T ω)) ^ 2 +
            2 * (f ω * birkhoffSum T f n (T ω)) + (f ω) ^ 2) := by
        funext ω; ring
      rw [hexp, integral_add
        (f := fun ω => (birkhoffSum T f n (T ω)) ^ 2 +
          2 * (f ω * birkhoffSum T f n (T ω)))
        (g := fun ω => (f ω) ^ 2)
        (hshift.integrable_sq.add (hprod.const_mul 2)) hf.integrable_sq,
        integral_add (f := fun ω => (birkhoffSum T f n (T ω)) ^ 2)
          (g := fun ω => 2 * (f ω * birkhoffSum T f n (T ω)))
          hshift.integrable_sq (hprod.const_mul 2), integral_const_mul,
        clock_correlation_integral_shift hT (hsum n).integrable_sq, hcross]
      congr 1
      simp only [c, Function.iterate_zero_apply, pow_two]
    have hC : (∑ k ∈ Finset.range n, |c k|) ≤
        ∑ k ∈ Finset.range (n + 1), |c k| := by
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (abs_nonneg _)
    have hstep : 2 * (∑ k ∈ Finset.range n, c (k + 1)) + c 0 ≤
        2 * ∑ k ∈ Finset.range (n + 1), |c k| := by
      rw [Finset.sum_range_succ']
      have hle := Finset.sum_le_sum (s := Finset.range n)
        (fun k _ => le_abs_self (c (k + 1)))
      rw [abs_of_nonneg hc0]
      linarith
    rw [hrec, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ 2 * (n : ℝ) * (∑ k ∈ Finset.range n, |c k|) +
          2 * ∑ k ∈ Finset.range (n + 1), |c k| := by linarith only [ih, hstep]
      _ ≤ 2 * (n : ℝ) * (∑ k ∈ Finset.range (n + 1), |c k|) +
          2 * ∑ k ∈ Finset.range (n + 1), |c k| :=
        add_le_add (mul_le_mul_of_nonneg_left hC
          (show (0 : ℝ) ≤ 2 * (n : ℝ) by positivity)) le_rfl
      _ = _ := by ring

/-- Cauchy–Schwarz against the constant function on a probability space. -/
private lemma clock_integral_abs_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : MemLp g 2 μ) :
    (∫ ω, |g ω| ∂μ) ^ 2 ≤ ∫ ω, (g ω) ^ 2 ∂μ := by
  let a : ℝ := ∫ ω, |g ω| ∂μ
  have ha : Integrable (fun ω => |g ω|) μ := by
    simpa only [Real.norm_eq_abs] using hg.norm.integrable (by norm_num)
  have hexp : (fun ω => (|g ω| - a) ^ 2) =
      (fun ω => (g ω) ^ 2 - (2 * a) * |g ω| + a ^ 2) := by
    funext ω
    nlinarith only [sq_abs (g ω)]
  have hpos := integral_nonneg (μ := μ)
    (f := fun ω : Ω => (|g ω| - a) ^ 2) (fun ω => sq_nonneg (|g ω| - a))
  rw [hexp, integral_add
    (f := fun ω => (g ω) ^ 2 - (2 * a) * |g ω|) (g := fun _ => a ^ 2)
    (hg.integrable_sq.sub (ha.const_mul _)) (integrable_const _),
    integral_sub (f := fun ω => (g ω) ^ 2) (g := fun ω => (2 * a) * |g ω|)
      hg.integrable_sq (ha.const_mul _), integral_const_mul, integral_const] at hpos
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hpos
  change a ^ 2 ≤ _
  change 0 ≤ (∫ ω, (g ω) ^ 2 ∂μ) - (2 * a) * a + a ^ 2 at hpos
  nlinarith only [hpos]

/-- Cesàro decay of absolute correlations implies L¹ decay of stationary
 Birkhoff averages for an almost-everywhere bounded real observable. -/
theorem clock_l1_mean_zero_of_abs_correlations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ᵐ ω ∂μ, |f ω| ≤ B)
    (hcorr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), |∫ ω, f ω * f ((T^[k]) ω) ∂μ|)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ ω,
      |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ∂μ) atTop (𝓝 0) := by
  have hf2 : MemLp f 2 μ :=
    MemLp.of_bound hf.aestronglyMeasurable |B| (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hB] using hbound)
  have hsq (n : ℕ) :
      (∫ ω, |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ∂μ) ^ 2 ≤
        2 * (((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1),
          |∫ ω, f ω * f ((T^[k]) ω) ∂μ|) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hs := clock_correlation_sum_memLp hT hf2 (n + 1)
    have h := clock_integral_abs_sq_le (hs.mul_const (((n : ℝ) + 1)⁻¹))
    simp only [div_eq_mul_inv] at ⊢
    refine h.trans ?_
    have hv := clock_correlation_second_moment hT hf2 (n + 1)
    rw [Nat.cast_add, Nat.cast_one] at hv
    simp_rw [mul_pow]
    rw [integral_mul_const]
    calc
      _ ≤ (2 * ((n : ℝ) + 1) * ∑ k ∈ Finset.range (n + 1),
          |∫ ω, f ω * f ((T^[k]) ω) ∂μ|) * (((n : ℝ) + 1)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right hv (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hn]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (2 * (((n : ℝ) + 1)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), |∫ ω, f ω * f ((T^[k]) ω) ∂μ|)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hcorr).sqrt
  exact squeeze_zero (fun n => integral_nonneg (fun ω => abs_nonneg _))
    (fun n => Real.le_sqrt_of_sq_le (hsq n)) hlim

/-- Exact stationary variance identity, expressed as a sum of correlation
 partial sums so that signed cancellation is retained. -/
private lemma clock_signed_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) (n : ℕ) :
    (∫ ω, (birkhoffSum T f n ω) ^ 2 ∂μ) =
      2 * (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range (j + 1),
        ∫ ω, f ω * f ((T^[k]) ω) ∂μ) -
      (n : ℝ) * (∫ ω, f ω * f ω ∂μ) := by
  let c : ℕ → ℝ := fun k => ∫ ω, f ω * f ((T^[k]) ω) ∂μ
  have hsum (m : ℕ) := clock_correlation_sum_memLp hT hf m
  have hcross (m : ℕ) :
      (∫ ω, f ω * birkhoffSum T f m (T ω) ∂μ) =
        ∑ k ∈ Finset.range m, c (k + 1) := by
    simp only [birkhoffSum, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [c, Function.iterate_succ_apply]
    · intro k hk
      exact hf.integrable_mul (hf.comp_measurePreserving ((hT.iterate k).comp hT))
  change (∫ ω, (birkhoffSum T f n ω) ^ 2 ∂μ) =
    2 * (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range (j + 1), c k) - (n : ℝ) * c 0
  induction n with
  | zero => simp only [birkhoffSum_zero_apply, zero_pow (by decide : 2 ≠ 0),
      integral_zero, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, mul_zero,
      zero_mul, sub_self]
  | succ n ih =>
    have hshift := (hsum n).comp_measurePreserving hT
    have hprod := hf.integrable_mul hshift
    have houter : (∑ j ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (j + 1), c k) =
        (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range (j + 1), c k) +
          ∑ k ∈ Finset.range (n + 1), c k := by
      rw [Finset.sum_range_succ]
    have hpartial : (∑ k ∈ Finset.range (n + 1), c k) =
        (∑ k ∈ Finset.range n, c (k + 1)) + c 0 := by
      rw [Finset.sum_range_succ']
    have hexp : (fun ω => (f ω + birkhoffSum T f n (T ω)) ^ 2) =
        (fun ω => (birkhoffSum T f n (T ω)) ^ 2 +
          2 * (f ω * birkhoffSum T f n (T ω)) + (f ω) ^ 2) := by
      funext ω; ring
    simp_rw [birkhoffSum_succ_apply']
    rw [hexp, integral_add
      (f := fun ω => (birkhoffSum T f n (T ω)) ^ 2 +
        2 * (f ω * birkhoffSum T f n (T ω)))
      (g := fun ω => (f ω) ^ 2)
      (hshift.integrable_sq.add (hprod.const_mul 2)) hf.integrable_sq,
      integral_add (f := fun ω => (birkhoffSum T f n (T ω)) ^ 2)
        (g := fun ω => 2 * (f ω * birkhoffSum T f n (T ω)))
        hshift.integrable_sq (hprod.const_mul 2), integral_const_mul,
      clock_correlation_integral_shift hT (hsum n).integrable_sq, hcross, ih,
      houter, hpartial, Nat.cast_add, Nat.cast_one]
    have hc : (∫ ω, (f ω) ^ 2 ∂μ) = c 0 := by
      simp only [c, Function.iterate_zero_apply, pow_two]
    rw [hc]
    ring

/-- Cesàro decay of signed correlations implies L¹ decay of stationary
 Birkhoff averages for an almost-everywhere bounded real observable. -/
theorem clock_l1_mean_zero_of_signed_correlations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ᵐ ω ∂μ, |f ω| ≤ B)
    (hcorr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), (∫ ω, f ω * f ((T^[k]) ω) ∂μ))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ ω,
      |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ∂μ) atTop (𝓝 0) := by
  have hf2 : MemLp f 2 μ :=
    MemLp.of_bound hf.aestronglyMeasurable |B| (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hB] using hbound)
  let A : ℕ → ℝ := fun j => ∑ k ∈ Finset.range (j + 1),
    ∫ ω, f ω * f ((T^[k]) ω) ∂μ
  let b : ℕ → ℝ := fun j => |((j : ℝ) + 1)⁻¹ * A j|
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [abs_zero] using hcorr.abs
  have hces : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ *
      ∑ j ∈ Finset.range (n + 1), b j) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hb.cesaro.comp (tendsto_add_atTop_nat 1)
  have hc0 : 0 ≤ (∫ ω, f ω * f ω ∂μ) :=
    integral_nonneg fun ω => mul_self_nonneg _
  have hvar (n : ℕ) : (∫ ω, (birkhoffSum T f (n + 1) ω) ^ 2 ∂μ) ≤
      2 * ((n : ℝ) + 1) * ∑ j ∈ Finset.range (n + 1), b j := by
    have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
        A j ≤ ((n : ℝ) + 1) * b j := by
      have hjn : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      have hjpos : 0 < (j : ℝ) + 1 := by positivity
      have hAj : |A j| = ((j : ℝ) + 1) * b j := by
        dsimp only [b]
        rw [abs_mul, abs_of_pos (inv_pos.mpr hjpos)]
        field_simp [ne_of_gt hjpos]
      exact (le_abs_self _).trans (hAj.le.trans
        (mul_le_mul_of_nonneg_right hjn (abs_nonneg _)))
    have hs := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hs
    rw [clock_signed_second_moment hT hf2, Nat.cast_add, Nat.cast_one]
    change 2 * (∑ j ∈ Finset.range (n + 1), A j) -
      ((n : ℝ) + 1) * (∫ ω, f ω * f ω ∂μ) ≤ _
    have hn : 0 ≤ ((n : ℝ) + 1) * (∫ ω, f ω * f ω ∂μ) :=
      mul_nonneg (by positivity) hc0
    linarith only [hs, hn]
  have hsq (n : ℕ) :
      (∫ ω, |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ∂μ) ^ 2 ≤
        2 * (((n : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), b j) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hs := clock_correlation_sum_memLp hT hf2 (n + 1)
    have h := clock_integral_abs_sq_le (hs.mul_const (((n : ℝ) + 1)⁻¹))
    simp only [div_eq_mul_inv]
    refine h.trans ?_
    simp_rw [mul_pow]
    rw [integral_mul_const]
    calc
      _ ≤ (2 * ((n : ℝ) + 1) * ∑ j ∈ Finset.range (n + 1), b j) *
          (((n : ℝ) + 1)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (hvar n) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hn]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (2 * (((n : ℝ) + 1)⁻¹ *
      ∑ j ∈ Finset.range (n + 1), b j))) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hces).sqrt
  exact squeeze_zero (fun n => integral_nonneg (fun ω => abs_nonneg _))
    (fun n => Real.le_sqrt_of_sq_le (hsq n)) hlim

/-- An exact L² transfer pairing carries decay of the transferred averages
to the signed Cesàro correlation criterion. -/
theorem clock_signed_correlations_of_l2_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (g : ℕ → Ω → ℝ)
    (hg : ∀ k, MemLp (g k) 2 μ)
    (hpair : ∀ k, (∫ ω, f ω * f ((T^[k]) ω) ∂μ) =
      ∫ ω, f ω * g k ω ∂μ)
    (hmean : Tendsto (fun n : ℕ => ∫ ω,
      (((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), g k ω)^2 ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), (∫ ω, f ω * f ((T^[k]) ω) ∂μ))
      atTop (𝓝 0) := by
  let G : ℕ → Ω → ℝ := fun n ω =>
    ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), g k ω
  have hG (n : ℕ) : MemLp (G n) 2 μ :=
    (memLp_finsetSum (Finset.range (n + 1)) (fun k _ => hg k)).const_mul _
  have hpairing (n : ℕ) :
      ((n : ℝ) + 1)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), (∫ ω, f ω * f ((T^[k]) ω) ∂μ) =
      ∫ ω, f ω * G n ω ∂μ := by
    have hexp : (fun ω => f ω * G n ω) =
        (fun ω => ((n : ℝ) + 1)⁻¹ *
          ∑ k ∈ Finset.range (n + 1), f ω * g k ω) := by
      funext ω
      dsimp only [G]
      rw [← Finset.mul_sum]
      ring
    rw [hexp, integral_const_mul,
      integral_finsetSum (Finset.range (n + 1)) (f := fun k ω => f ω * g k ω)
        (fun k _ => hf.integrable_mul (hg k))]
    exact congrArg (((n : ℝ) + 1)⁻¹ * ·)
      (Finset.sum_congr rfl (fun k _ => hpair k))
  have hbound (n : ℕ) :
      |((n : ℝ) + 1)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), (∫ ω, f ω * f ((T^[k]) ω) ∂μ)| ≤
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (G n ω)^2 ∂μ) := by
    rw [hpairing]
    have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (show MemLp f (ENNReal.ofReal (2 : ℝ)) μ by simpa using hf)
      (show MemLp (G n) (ENNReal.ofReal (2 : ℝ)) μ by simpa using hG n)
    have hnorm := norm_integral_le_integral_norm (fun ω => f ω * G n ω) (μ := μ)
    simp only [norm_mul, Real.norm_eq_abs] at hnorm hholder
    simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at hholder
    exact hnorm.trans hholder
  have hlim : Tendsto (fun n : ℕ =>
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (G n ω)^2 ∂μ))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds (x := Real.sqrt (∫ ω, (f ω)^2 ∂μ))).mul hmean.sqrt
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
    (squeeze_zero (fun _ => abs_nonneg _) hbound hlim)

end EinsteinFull.Blueprint
