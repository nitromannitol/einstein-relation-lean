import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Holder
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Elementary bounds for the dyadic scalar sums in Step 5 of Proposition 6.1
(paper/main.tex:1070-1078).

The scales are `r = 2^k` for `k < K`, that is `r = 1, 2, 4, …, R/2` with `R = 2^K`.
The first part bounds the scalar sums over these scales: the sum of
`√log(2 + r) / r` is bounded uniformly in `K`, and the sum of `r + √log(2 + r)`
is at most a constant times `R`. The second part is the Hölder step with moment
order `4p` on the factors and `2p` on the product, followed by the triangle
inequality over a finite sum. Only Mathlib is imported. -/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-! ### Scalar bounds over the dyadic scales -/

/-- The logarithm of `2 + 2^k` is at most `k + 2`, since `2 + 2^k ≤ 2^(k+2)`. -/
theorem log_dyadic_add_le (k : ℕ) : Real.log (2 + (2:ℝ) ^ k) ≤ (k:ℝ) + 2 := by
  have hge : (1:ℝ) ≤ (2:ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hpow : (2:ℝ) ^ (k + 2) = 2 ^ k * 4 := by
    rw [pow_add]; norm_num
  have hle : (2:ℝ) + 2 ^ k ≤ 2 ^ (k + 2) := by
    rw [hpow]; linarith
  have hlog : Real.log (2 + (2:ℝ) ^ k) ≤ Real.log ((2:ℝ) ^ (k + 2)) :=
    Real.log_le_log (by positivity) hle
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hmul := mul_le_of_le_one_right (by positivity : (0:ℝ) ≤ (k:ℝ) + 2) hlog2
  linarith

/-- The square root of the dyadic logarithm is at most `k + 3`. -/
theorem sqrt_log_dyadic_le (k : ℕ) :
    Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) ≤ (k:ℝ) + 3 := by
  have hlog := log_dyadic_add_le k
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hsq : Real.log (2 + (2:ℝ) ^ k) ≤ ((k:ℝ) + 3) ^ 2 := by
    nlinarith [sq_nonneg (k:ℝ)]
  calc Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) ≤ Real.sqrt (((k:ℝ) + 3) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = (k:ℝ) + 3 := Real.sqrt_sq (by positivity)

/-- The linear index is dominated by a multiple of `2^k`. -/
theorem add_three_le_three_mul_two_pow (k : ℕ) : (k:ℝ) + 3 ≤ 3 * (2:ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    have hge : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hpow : (2:ℝ) ^ (n + 1) = 2 ^ n * 2 := by ring
    rw [hpow]
    push_cast
    linarith

/-- The linear index is dominated by a multiple of `(3/2)^k`. -/
theorem add_three_le_three_mul_three_halves_pow (k : ℕ) :
    (k:ℝ) + 3 ≤ 3 * ((3:ℝ) / 2) ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    have hge : (1:ℝ) ≤ ((3:ℝ) / 2) ^ n := one_le_pow₀ (by norm_num)
    have hpow : ((3:ℝ) / 2) ^ (n + 1) = ((3:ℝ) / 2) ^ n * (3 / 2) := by ring
    rw [hpow]
    push_cast
    linarith

/-- Each dyadic term `√log(2 + 2^k) / 2^k` is at most `3 (3/4)^k`. -/
theorem sqrt_log_div_dyadic_le_geom (k : ℕ) :
    Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) / (2:ℝ) ^ k ≤ 3 * ((3:ℝ) / 4) ^ k := by
  have h1 := sqrt_log_dyadic_le k
  have h2 := add_three_le_three_mul_three_halves_pow k
  have hpos : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have h3 : ((3:ℝ) / 4) ^ k * (2:ℝ) ^ k = ((3:ℝ) / 2) ^ k := by
    rw [← mul_pow]; norm_num
  rw [div_le_iff₀ hpos]
  linarith

/-- Induction invariant for the dyadic sum: the partial sums stay below `12` minus
a geometrically decaying remainder. -/
theorem dyadic_sum_sqrtLog_div_aux (K : ℕ) :
    ∑ k ∈ Finset.range K, Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) / (2:ℝ) ^ k
      + 12 * ((3:ℝ) / 4) ^ K ≤ 12 := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpow : ((3:ℝ) / 4) ^ (n + 1) = ((3:ℝ) / 4) ^ n * (3 / 4) := by ring
    rw [hpow]
    have ht := sqrt_log_div_dyadic_le_geom n
    linarith

/-- The dyadic sum of `√log(2 + r) / r` over `r = 2^k`, `k < K`, is at most `12`. -/
theorem dyadic_sum_sqrtLog_div_le_twelve (K : ℕ) :
    ∑ k ∈ Finset.range K, Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) / (2:ℝ) ^ k ≤ 12 := by
  have h := dyadic_sum_sqrtLog_div_aux K
  have hnn : (0:ℝ) ≤ ((3:ℝ) / 4) ^ K := by positivity
  linarith

/-- Step 5 of Proposition 6.1: the dyadic sum of `√log(2 + r) / r` over `r = 2^k` is
bounded uniformly in the number of scales. -/
theorem dyadic_sum_sqrtLog_div_le :
    ∃ C : ℝ, ∀ K : ℕ,
      ∑ k ∈ Finset.range K, Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) / (2:ℝ) ^ k ≤ C :=
  ⟨12, dyadic_sum_sqrtLog_div_le_twelve⟩

/-- Each scale term `2^k + √log(2 + 2^k)` is at most `4 · 2^k`. -/
theorem two_pow_add_sqrtLog_le (k : ℕ) :
    (2:ℝ) ^ k + Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) ≤ 4 * (2:ℝ) ^ k := by
  have h1 := sqrt_log_dyadic_le k
  have h2 := add_three_le_three_mul_two_pow k
  linarith

/-- Induction invariant for the scale sum `∑_{k<K} (2^k + √log(2 + 2^k))`. -/
theorem dyadic_sum_scale_aux (K : ℕ) :
    ∑ k ∈ Finset.range K, ((2:ℝ) ^ k + Real.sqrt (Real.log (2 + (2:ℝ) ^ k)))
      ≤ 4 * (2:ℝ) ^ K - 4 := by
  induction K with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpow : (2:ℝ) ^ (n + 1) = 2 ^ n * 2 := by ring
    rw [hpow]
    have ht := two_pow_add_sqrtLog_le n
    linarith

/-- The scale sum `∑_{k<K} (2^k + √log(2 + 2^k))` is at most `4 · 2^K`, which is
`R`-linear for `R = 2^K`. -/
theorem dyadic_sum_scale_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((2:ℝ) ^ k + Real.sqrt (Real.log (2 + (2:ℝ) ^ k)))
      ≤ 4 * (2:ℝ) ^ K := by
  have h := dyadic_sum_scale_aux K
  linarith

/-- The number of dyadic scales is at most `2 log(2 + 2^K)`, since `log 2 > 1/2`. -/
theorem dyadic_count_le_log (K : ℕ) : (K:ℝ) ≤ 2 * Real.log (2 + (2:ℝ) ^ K) := by
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    have h' : (0.6931471803 : ℝ) > 1 / 2 := by norm_num
    linarith
  have hKlog : Real.log ((2:ℝ) ^ K) ≤ Real.log (2 + (2:ℝ) ^ K) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_pow] at hKlog
  have hK : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hmul := mul_le_mul_of_nonneg_left hlog2 hK
  linarith

/-! ### Hölder step and triangle inequality -/

/-- Hölder's inequality with moment order `4p` on the factors and `2p` on the product,
for real-valued functions on an arbitrary measure space. -/
theorem eLpNorm_mul_le_holder_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 1 ≤ p) {X Y : Ω → ℝ} (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) :
    eLpNorm (fun ω => X ω * Y ω) (ENNReal.ofReal (2 * p)) μ ≤
      eLpNorm X (ENNReal.ofReal (4 * p)) μ * eLpNorm Y (ENNReal.ofReal (4 * p)) μ := by
  have h2 : (0:ℝ) < 2 * p := by linarith
  have h4 : (0:ℝ) < 4 * p := by linarith
  have hsum : (ENNReal.ofReal (4 * p))⁻¹ + (ENNReal.ofReal (4 * p))⁻¹ =
      (ENNReal.ofReal (2 * p))⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos h4, ← ENNReal.ofReal_inv_of_pos h2,
      ← ENNReal.ofReal_add (inv_nonneg.mpr h4.le) (inv_nonneg.mpr h4.le)]
    congr 1
    ring
  have hr : ((ENNReal.ofReal (4 * p))⁻¹ + (ENNReal.ofReal (4 * p))⁻¹)⁻¹ =
      ENNReal.ofReal (2 * p) := by
    rw [hsum, inv_inv]
  have hT := ENNReal.HolderTriple.of (ENNReal.ofReal (4 * p)) (ENNReal.ofReal (4 * p))
  rw [hr] at hT
  haveI : ENNReal.HolderTriple (ENNReal.ofReal (4 * p)) (ENNReal.ofReal (4 * p))
      (ENNReal.ofReal (2 * p)) := hT
  have hb : ∀ᵐ ω ∂μ, ‖(fun a b : ℝ => a * b) (X ω) (Y ω)‖₊ ≤
      (1 : NNReal) * ‖X ω‖₊ * ‖Y ω‖₊ :=
    ae_of_all μ fun ω => by simp only [nnnorm_mul, one_mul, le_refl]
  have h : eLpNorm (fun ω => X ω * Y ω) (ENNReal.ofReal (2 * p)) μ ≤
      ((1 : NNReal) : ℝ≥0∞) * eLpNorm X (ENNReal.ofReal (4 * p)) μ *
        eLpNorm Y (ENNReal.ofReal (4 * p)) μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hX hY (fun a b : ℝ => a * b) 1 hb
  simpa only [ENNReal.coe_one, one_mul] using h

/-- Triangle inequality for a finite sum of real-valued functions in `L^p`, `1 ≤ p`. -/
theorem eLpNorm_finset_sum_le {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (s : Finset ι) (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ)
    (hp : 1 ≤ p) :
    eLpNorm (fun ω => ∑ i ∈ s, f i ω) p μ ≤ ∑ i ∈ s, eLpNorm (f i) p μ := by
  have hfun : (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i := (Finset.sum_fn s f).symm
  rw [hfun]
  exact eLpNorm_sum_le hf hp

/-- Hölder's inequality for a finite sum of products `∑_{i ∈ s} X_i Y_i`, with the
entrywise bound by products of `4p` norms. -/
theorem eLpNorm_sum_mul_le_holder {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 1 ≤ p) (s : Finset ι) (X Y : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i ∈ s, AEStronglyMeasurable (Y i) μ) :
    eLpNorm (fun ω => ∑ i ∈ s, X i ω * Y i ω) (ENNReal.ofReal (2 * p)) μ ≤
      ∑ i ∈ s, eLpNorm (X i) (ENNReal.ofReal (4 * p)) μ *
        eLpNorm (Y i) (ENNReal.ofReal (4 * p)) μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) :=
    ENNReal.one_le_ofReal.mpr (by linarith)
  calc eLpNorm (fun ω => ∑ i ∈ s, X i ω * Y i ω) (ENNReal.ofReal (2 * p)) μ
      ≤ ∑ i ∈ s, eLpNorm (fun ω => X i ω * Y i ω) (ENNReal.ofReal (2 * p)) μ :=
        eLpNorm_finset_sum_le s (fun i ω => X i ω * Y i ω)
          (fun i hi => (hX i hi).mul (hY i hi)) hp1
    _ ≤ ∑ i ∈ s, eLpNorm (X i) (ENNReal.ofReal (4 * p)) μ *
          eLpNorm (Y i) (ENNReal.ofReal (4 * p)) μ :=
        Finset.sum_le_sum fun i hi => eLpNorm_mul_le_holder_four hp (hX i hi) (hY i hi)

/-- Vector form: the `2p` norm of a dot product of `Fin d`-valued random vectors is at
most the sum of products of their entrywise `4p` norms. -/
theorem eLpNorm_dotProduct_le_holder {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x y : Ω → Fin d → ℝ)
    (hx : ∀ i, AEStronglyMeasurable (fun ω => x ω i) μ)
    (hy : ∀ i, AEStronglyMeasurable (fun ω => y ω i) μ) :
    eLpNorm (fun ω => dotProduct (x ω) (y ω)) (ENNReal.ofReal (2 * p)) μ ≤
      ∑ i : Fin d, eLpNorm (fun ω => x ω i) (ENNReal.ofReal (4 * p)) μ *
        eLpNorm (fun ω => y ω i) (ENNReal.ofReal (4 * p)) μ := by
  have h := eLpNorm_sum_mul_le_holder hp (Finset.univ : Finset (Fin d))
    (fun i ω => x ω i) (fun i ω => y ω i) (fun i _ => hx i) (fun i _ => hy i)
  exact h

/-- Vector form for matrix-vector products: an entry `i` of `M(ω) v(ω)` has `2p` norm at
most the sum of products of the entrywise `4p` norms of `M(·)_{ij}` and `v(·)_j`. -/
theorem eLpNorm_mulVec_entry_le_holder {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (M : Ω → Matrix (Fin d) (Fin d) ℝ)
    (v : Ω → Fin d → ℝ) (i : Fin d)
    (hM : ∀ j, AEStronglyMeasurable (fun ω => M ω i j) μ)
    (hv : ∀ j, AEStronglyMeasurable (fun ω => v ω j) μ) :
    eLpNorm (fun ω => Matrix.mulVec (M ω) (v ω) i) (ENNReal.ofReal (2 * p)) μ ≤
      ∑ j : Fin d, eLpNorm (fun ω => M ω i j) (ENNReal.ofReal (4 * p)) μ *
        eLpNorm (fun ω => v ω j) (ENNReal.ofReal (4 * p)) μ := by
  have h := eLpNorm_sum_mul_le_holder hp (Finset.univ : Finset (Fin d))
    (fun j ω => M ω i j) (fun j ω => v ω j) (fun j _ => hM j) (fun j _ => hv j)
  exact h

/-! ### The combined dyadic estimate -/

/-- Step 5 of Proposition 6.1. If `‖X_{2^k}‖_{4p} ≤ A √log(2 + 2^k)` and
`‖Y_{2^k}‖_{4p} ≤ B / 2^k` for every `k`, then the `2p` norm of the dyadic sum
`∑_{k<K} X_{2^k} Y_{2^k}` is at most `12 A B`. -/
theorem eLpNorm_dyadic_sum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p A B : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B) (K : ℕ)
    (X Y : ℕ → Ω → ℝ) (hX : ∀ k, AEStronglyMeasurable (X k) μ)
    (hY : ∀ k, AEStronglyMeasurable (Y k) μ)
    (hXb : ∀ k : ℕ, eLpNorm (X k) (ENNReal.ofReal (4 * p)) μ ≤
      ENNReal.ofReal (A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k))))
    (hYb : ∀ k : ℕ, eLpNorm (Y k) (ENNReal.ofReal (4 * p)) μ ≤
      ENNReal.ofReal (B / (2:ℝ) ^ k)) :
    eLpNorm (fun ω => ∑ k ∈ Finset.range K, X k ω * Y k ω) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal (A * B * 12) := by
  have hterm : ∀ k ∈ Finset.range K,
      eLpNorm (fun ω => X k ω * Y k ω) (ENNReal.ofReal (2 * p)) μ ≤
        ENNReal.ofReal (A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) * (B / (2:ℝ) ^ k)) := by
    intro k _
    have hnn : 0 ≤ A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) :=
      mul_nonneg hA (Real.sqrt_nonneg _)
    calc eLpNorm (fun ω => X k ω * Y k ω) (ENNReal.ofReal (2 * p)) μ
        ≤ eLpNorm (X k) (ENNReal.ofReal (4 * p)) μ *
            eLpNorm (Y k) (ENNReal.ofReal (4 * p)) μ :=
          eLpNorm_mul_le_holder_four hp (hX k) (hY k)
      _ ≤ ENNReal.ofReal (A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k))) *
            ENNReal.ofReal (B / (2:ℝ) ^ k) :=
          mul_le_mul_of_nonneg' (hXb k) (hYb k) (zero_le _) (zero_le _)
      _ = ENNReal.ofReal (A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) * (B / (2:ℝ) ^ k)) :=
          (ENNReal.ofReal_mul hnn).symm
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) :=
    ENNReal.one_le_ofReal.mpr (by linarith)
  have hnonneg : ∀ k ∈ Finset.range K,
      0 ≤ A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) * (B / (2:ℝ) ^ k) := by
    intro k _
    exact mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg _))
      (div_nonneg hB (by positivity))
  have hreal : ∑ k ∈ Finset.range K,
      A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) * (B / (2:ℝ) ^ k) =
        A * B * ∑ k ∈ Finset.range K, Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) / (2:ℝ) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hbound : ∑ k ∈ Finset.range K,
      A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) * (B / (2:ℝ) ^ k) ≤ A * B * 12 := by
    rw [hreal]
    exact mul_le_mul_of_nonneg_left (dyadic_sum_sqrtLog_div_le_twelve K) (mul_nonneg hA hB)
  calc eLpNorm (fun ω => ∑ k ∈ Finset.range K, X k ω * Y k ω) (ENNReal.ofReal (2 * p)) μ
      ≤ ∑ k ∈ Finset.range K, eLpNorm (fun ω => X k ω * Y k ω) (ENNReal.ofReal (2 * p)) μ :=
        eLpNorm_finset_sum_le (Finset.range K) (fun k ω => X k ω * Y k ω)
          (fun k _ => (hX k).mul (hY k)) hp1
    _ ≤ ∑ k ∈ Finset.range K,
          ENNReal.ofReal (A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) * (B / (2:ℝ) ^ k)) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ k ∈ Finset.range K,
          A * Real.sqrt (Real.log (2 + (2:ℝ) ^ k)) * (B / (2:ℝ) ^ k)) :=
        (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
    _ ≤ ENNReal.ofReal (A * B * 12) := ENNReal.ofReal_le_ofReal hbound

end EinsteinRelation.Correctors
